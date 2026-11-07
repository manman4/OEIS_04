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

/* Usage: 400702_01 n. The b-file in the current directory is the resume record. */
/* At most 15 elements and 120 pairs. Candidate sums are at most 510,
   and only sums at most n index the seen array. */
enum { MAX_N = 255, MAX_SIZE = 15 };
static const char output[] = "b400702.txt";

typedef struct {
    int n, size;
    int chosen[MAX_SIZE];
    unsigned char seen[MAX_N + 1];
} Search;

static int subset_size(int n)
{
    int k = 1;
    while ((k + 1) * (k + 1) <= n)
        ++k;
    return k;
}

static int pair_count(int k)
{
    return k * (k + 1) / 2;
}

/* A loss is a pair whose sum is out of range or already represented. */
static int feasible(Search *s, int depth, int first, int budget)
{
    if (depth == s->size)
        return 1;

    /* The smallest possible completion bounds future out-of-range pairs. */
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
        s->chosen[depth] = x;
        int last = depth;
        while (last >= 0 && s->chosen[last] + x > s->n)
            --last;
        int loss = depth - last;
        if (loss > budget)
            break; /* Out-of-range pair count is nondecreasing in x. */

        int added[MAX_SIZE], count = 0;
        for (int j = 0; j <= last; ++j) {
            int sum = s->chosen[j] + x;
            if (s->seen[sum]) {
                ++loss;
            } else {
                s->seen[sum] = 1;
                added[count++] = sum;
            }
        }
        int found = loss <= budget && feasible(s, depth + 1, x + 1, budget - loss);
        while (count > 0)
            s->seen[added[--count]] = 0;
        if (found)
            return 1;
    }
    return 0;
}

static int term(int n)
{
    if (n == 1)
        return 0;
    Search s = { .n = n, .size = subset_size(n), .chosen = { 1 } };
    s.seen[2] = 1;
    /* Translate the minimum to 1. For n >= 2, n adds no counted sum
       and can be replaced by an unused element of {1, ..., n-1}. */
    int pairs = pair_count(s.size);
    for (int budget = 0; budget < pairs; ++budget)
        if (feasible(&s, 1, 2, budget))
            return pairs - budget;
    return 0;
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
    char temporary[] = ".b400702.txt.XXXXXX";
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
        fprintf(stderr, "Usage: 400702_01 n (1 <= n <= %d)\n", MAX_N);
        return EXIT_FAILURE;
    }
    errno = 0;
    long limit = strtol(argv[1], &end, 10);
    if (argv[1][0] < '0' || argv[1][0] > '9' || *end || errno ||
        limit < 1 || limit > MAX_N) {
        fprintf(stderr, "n must be an integer from 1 to %d.\n", MAX_N);
        return EXIT_FAILURE;
    }

    /* Lock the directory inode so the lock survives replacing the b-file. */
    int lock = open(".", O_RDONLY | O_DIRECTORY);
    if (lock < 0) {
        perror("open output directory");
        return EXIT_FAILURE;
    }
    if (flock(lock, LOCK_EX | LOCK_NB) != 0) {
        perror("lock output directory");
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
        for (int n = count + 1; n <= limit; ++n) {
            values[n] = term(n);
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
