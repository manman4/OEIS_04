#define _DARWIN_C_SOURCE
#define _DEFAULT_SOURCE
#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>

/* Usage: 400702_02 n. The b-file in the current directory is the resume record.
   Existing values are checked for format and bounds, not reproved on restart.
   Saved values are never used as search bounds for later terms.
   Support is 1..255; exhaustive search may be expensive near perfect squares. */
/* At most 15 elements and 120 pairs. Candidate sums are at most 510,
   and only sums at most n index the seen array. */
   
enum { MAX_N = 255, MAX_SIZE = 15 };
static const char output[] = "b400702_02.txt";

#include <stdint.h>

typedef struct { uint64_t word[4]; } Bits;
typedef struct {
    int n, size, words;
    int chosen[MAX_SIZE], best[MAX_SIZE];
    Bits allowed;
} Search;

static int subset_size(int n)
{
    int k = 1;
    while ((k + 1) * (k + 1) <= n)
        ++k;
    return k;
}

static int pair_count(int k) { return k * (k + 1) / 2; }

static void set_bit(Bits *bits, int bit)
{
    bits->word[bit / 64] |= UINT64_C(1) << (bit % 64);
}

static Bits pair_sums(const Search *s, Bits elements, int x)
{
    Bits result = {{0}};
    int whole = x / 64, part = x % 64;
    for (int w = whole; w < s->words; ++w) {
        uint64_t low = elements.word[w - whole];
        if (part)
            low = (low & (UINT64_MAX >> part)) << part;
        result.word[w] = low;
        if (part && w > whole)
            result.word[w] |= elements.word[w - whole - 1] >> (64 - part);
        result.word[w] &= s->allowed.word[w];
    }
    if (2 * x <= s->n)
        set_bit(&result, 2 * x);
    return result;
}

static int new_count(const Search *s, Bits added, Bits sums)
{
    int count = 0;
    for (int w = 0; w < s->words; ++w)
        count += __builtin_popcountll(added.word[w] & ~sums.word[w]);
    return count;
}

static Bits unite(const Search *s, Bits a, Bits b)
{
    for (int w = 0; w < s->words; ++w)
        a.word[w] |= b.word[w];
    return a;
}

/* If no pair can be lost, all positive differences must be distinct.
   For q neighboring gaps, D=q*k-q*(q+1)/2 differences have total at
   least D*(D+1)/2 and at most q*(q+1)/2 times the span. */
static int sidon_span_bound(int k)
{
    int bound = 0;
    for (int q = 1; q < k; ++q) {
        int d = q * k - q * (q + 1) / 2, divisor = q * (q + 1);
        int lower = (d * (d + 1) + divisor - 1) / divisor;
        if (lower > bound)
            bound = lower;
    }
    return bound;
}

/* A pair loses one unit if it is out of range or repeats an existing sum. */
static int feasible(Search *s, int depth, int first,
                    Bits elements, Bits sums, int budget)
{
    if (depth == s->size)
        return 1;
    int forced = 0;
    for (int i = depth; i < s->size; ++i) {
        int x = first + i - depth;
        for (int j = 0; j < depth; ++j)
            forced += s->chosen[j] + x > s->n;
        for (int j = depth; j <= i; ++j)
            forced += first + j - depth + x > s->n;
        if (forced > budget)
            return 0;
    }
    int limit = s->n - s->size + depth;
    for (int x = first; x <= limit; ++x) {
        Bits added = pair_sums(s, elements, x);
        int in_range = 0;
        for (int w = 0; w < s->words; ++w)
            in_range += __builtin_popcountll(added.word[w]);
        if (depth + 1 - in_range > budget)
            break;
        int loss = depth + 1 - new_count(s, added, sums);
        if (loss > budget)
            continue;
        Bits next = elements;
        set_bit(&next, x);
        s->chosen[depth] = x;
        if (feasible(s, depth + 1, x + 1, next, unite(s, sums, added), budget - loss))
            return 1;
    }
    return 0;
}

static unsigned random_number(uint64_t *state)
{
    *state = (*state * UINT64_C(16807)) % UINT64_C(2147483647);
    return (unsigned)*state;
}

static int score(const Search *s, const int a[MAX_SIZE])
{
    unsigned char member[MAX_N + 1] = {0}, seen[MAX_N + 1] = {0};
    for (int i = 0; i < s->size; ++i) {
        if (a[i] < 1 || a[i] >= s->n || member[a[i]])
            abort();
        member[a[i]] = 1;
    }
    int total = 0;
    for (int i = 0; i < s->size; ++i)
        for (int j = i; j < s->size; ++j) {
            int sum = a[i] + a[j];
            if (sum <= s->n && !seen[sum]) {
                seen[sum] = 1;
                ++total;
            }
        }
    return total;
}

/* A bounded deterministic heuristic supplies only a lower-bound witness.
   Its random state is in 1..2147483646, so multiplication by 16807
   is below 2^46. No wraparound arithmetic is required. */
static int initial_witness(Search *s, const int previous[MAX_SIZE])
{
    int a[MAX_SIZE] = {0}, multiplicity[MAX_N + 1] = {0};
    if (previous && !previous[s->size - 1] && s->size > 1 &&
        previous[s->size - 2]) {
        memcpy(a, previous, (size_t)(s->size - 1) * sizeof *a);
        int best_value = -1, best_x = 0;
        for (int x = 2; x < s->n; ++x) {
            int used = 0;
            for (int i = 0; i < s->size - 1; ++i)
                used |= a[i] == x;
            if (!used) {
                a[s->size - 1] = x;
                int value = score(s, a);
                if (value > best_value) {
                    best_value = value;
                    best_x = x;
                }
            }
        }
        a[s->size - 1] = best_x;
    } else {
        for (int i = 0; i < s->size; ++i)
            a[i] = previous && previous[s->size - 1] ? previous[i] : i + 1;
    }
    unsigned char member[MAX_N + 1] = {0};
    for (int i = 0; i < s->size; ++i) {
        member[a[i]] = 1;
    }
    int current = 0;
    for (int i = 0; i < s->size; ++i)
        for (int j = i; j < s->size; ++j) {
            int sum = a[i] + a[j];
            if (sum <= s->n && multiplicity[sum]++ == 0)
                ++current;
        }
    int best = current;
    memcpy(s->best, a, sizeof a);
    if (best == pair_count(s->size) || s->size < 2)
        return best;
    uint64_t state = (uint64_t)s->n + 1;
    int maximum = s->n - 1;

    for (int step = 0; step < 200000; ++step) {
        int at = 1 + (int)(random_number(&state) % (unsigned)(s->size - 1));
        int x = 2 + (int)(random_number(&state) % (unsigned)(maximum - 1));
        if (member[x])
            continue;
        int old = a[at], before = current;
        for (int j = 0; j < s->size; ++j) {
            int sum = old + a[j];
            if (sum <= s->n && --multiplicity[sum] == 0)
                --current;
        }
        a[at] = x;
        for (int j = 0; j < s->size; ++j) {
            int sum = x + a[j];
            if (sum <= s->n && multiplicity[sum]++ == 0)
                ++current;
        }
        int drop = before - current;
        unsigned chance = (unsigned)(2 + step % 10000 / 700), denominator = 1;
        if (drop > 0 && drop <= 3)
            for (int j = 0; j < drop; ++j)
                denominator *= chance;
        int accept = drop <= 0 ||
            (drop <= 3 && random_number(&state) % denominator == 0);
        if (accept) {
            member[old] = 0;
            member[x] = 1;
            if (current > best) {
                best = current;
                memcpy(s->best, a, sizeof a);
                if (best == pair_count(s->size))
                    break;
            }
        } else {
            for (int j = 0; j < s->size; ++j) {
                int sum = x + a[j];
                if (sum <= s->n)
                    --multiplicity[sum];
            }
            a[at] = old;
            for (int j = 0; j < s->size; ++j) {
                int sum = old + a[j];
                if (sum <= s->n)
                    ++multiplicity[sum];
            }
            current = before;
        }
    }
    return best;
}

static int term(int n, int previous[MAX_SIZE])
{
    if (n == 1) {
        previous[0] = 1;
        return 0;
    }
    Search s = { .n = n, .size = subset_size(n), .words = n / 64 + 1 };
    for (int x = 0; x <= n; ++x)
        set_bit(&s.allowed, x);
    int upper = pair_count(s.size);
    if (sidon_span_bound(s.size) > n / 2 - 1)
        --upper;
    Bits elements = {{2}}, sums = {{4}};
    s.chosen[0] = 1;
    if (upper == pair_count(s.size)) {
        if (feasible(&s, 1, 2, elements, sums, 0)) {
            memcpy(previous, s.chosen, sizeof s.chosen);
            return upper;
        }
        --upper;
    }
    int best = initial_witness(&s, previous);
    if (score(&s, s.best) != best)
        abort();
    if (best > upper)
        abort();
    /* Any solution with a larger score also meets this threshold.
       Exhausting this search proves the current witnessed score optimal. */
    while (best < upper &&
           feasible(&s, 1, 2, elements, sums, pair_count(s.size) - best - 1)) {
        memcpy(s.best, s.chosen, sizeof s.best);
        int improved = score(&s, s.best);
        if (improved <= best)
            abort();
        best = improved;
    }
    memcpy(previous, s.best, sizeof s.best);
    return best;
}

/* Accept only a contiguous prefix in the format this program writes. */
static int load_prefix(int values[MAX_N + 1])
{
    int fd = open(output, O_RDONLY | O_NOFOLLOW | O_NONBLOCK);
    if (fd < 0)
        return errno == ENOENT ? 0 : -1;
    struct stat info;
    if (fstat(fd, &info) != 0 || !S_ISREG(info.st_mode)) {
        close(fd);
        return -1;
    }
    FILE *file = fdopen(fd, "r");
    if (!file) {
        close(fd);
        return -1;
    }
    char line[64], expected[64];
    int count = 0;
    while (fgets(line, sizeof line, file)) {
        if (count == MAX_N) {
            count = -1;
            break;
        }
        int index = count + 1;
        int max_value = index == 1 ? 0 : pair_count(subset_size(index));
        int value = index == 1 ? 0 : (values[count] > 0 ? values[count] : 1);
        for (; value <= max_value; ++value) {
            snprintf(expected, sizeof expected, "%d %d\n", index, value);
            if (strcmp(line, expected) == 0)
                break;
        }
        if (value > max_value) {
            count = -1;
            break;
        }
        values[++count] = value;
    }
    if (ferror(file))
        count = -1;
    if (fclose(file) != 0)
        count = -1;
    return count;
}

static int save_prefix(const int values[MAX_N + 1], int count)
{
    char temporary[] = ".b400702_02.txt.XXXXXX";
    int fd = mkstemp(temporary);
    if (fd < 0)
        return -1;
    FILE *file = fdopen(fd, "w");
    int ok = file != NULL;
    if (file) {
        for (int i = 1; i <= count && ok; ++i)
            ok = fprintf(file, "%d %d\n", i, values[i]) >= 0;
        if (ok)
            ok = fflush(file) == 0 && fsync(fd) == 0;
        if (fclose(file) != 0)
            ok = 0;
    } else {
        close(fd);
    }
    if (ok && rename(temporary, output) == 0)
        return 0;
    unlink(temporary);
    return -1;
}

int main(int argc, char **argv)
{
    char *end;
    if (argc != 2) {
        fprintf(stderr, "Usage: 400702_02 n (1 <= n <= %d)\n", MAX_N);
        return EXIT_FAILURE;
    }
    errno = 0;
    long limit = strtol(argv[1], &end, 10);
    if (argv[1][0] < '0' || argv[1][0] > '9' || *end || errno ||
        limit < 1 || limit > MAX_N) {
        fprintf(stderr, "n must be an integer from 1 to %d.\n", MAX_N);
        return EXIT_FAILURE;
    }

    /* Keep this inode stable across atomic replacements of the b-file.
       An unlocked lock file can remain after normal termination. */
    int lock = open("b400702_02.txt.lock",
                    O_RDWR | O_CREAT | O_NOFOLLOW | O_NONBLOCK, 0600);
    if (lock < 0) {
        perror("open output lock");
        return EXIT_FAILURE;
    }
    struct stat lock_info;
    if (fstat(lock, &lock_info) != 0 || !S_ISREG(lock_info.st_mode)) {
        fprintf(stderr, "Output lock must be a regular file.\n");
        close(lock);
        return EXIT_FAILURE;
    }
    if (flock(lock, LOCK_EX | LOCK_NB) != 0) {
        perror("lock output");
        close(lock);
        return EXIT_FAILURE;
    }

    int values[MAX_N + 1];
    int count = load_prefix(values);
    int status = EXIT_SUCCESS;
    if (count < 0) {
        fprintf(stderr, "Cannot read a valid consecutive prefix from %s.\n", output);
        status = EXIT_FAILURE;
    } else {
        int previous[MAX_SIZE] = {0};
        for (int n = count + 1; n <= limit; ++n) {
            values[n] = term(n, previous);
            if (save_prefix(values, n) != 0) {
                fprintf(stderr, "Could not save %s at n=%d.\n", output, n);
                status = EXIT_FAILURE;
                break;
            }
            printf("%d %d\n", n, values[n]);
            fflush(stdout);
        }
    }
    close(lock);
    return status;
}
