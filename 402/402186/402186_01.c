/*
 * A402186 / Erdős Problem 160.  Usage: 402186_01 NMAX [SECONDS_PER_TERM]
 * Print one "n a(n)" row per completed term.  The optional limit defaults
 * to 60 seconds.  A timed-out term produces no row and exits with status 2.
 *
 * A restriction to a shorter interval is still valid, so the previous
 * minimum is a lower bound.  Try the previous witness with one added point,
 * and otherwise test palettes in increasing order by exact search.
 *
 * Search in position order.  As soon as the first three points of a
 * progression are assigned, one colour is impossible to complete, two
 * colours forbid those two at the fourth point, and three impose no
 * restriction.  Intersect the fourth point's domain with this restriction
 * and undo the change on backtracking.  No later choice can repair an empty
 * domain.  By renaming colours in first-use order, only the next unused
 * colour needs to be tried alongside previously used colours.
 *
 * At most 64 positions or colours are handled.  All positions are 0-based
 * internally.  For x as a third position, d <= x/2 and d <= n-1-x, so all
 * accesses to x-2*d, x-d and x+d are within 0..n-1.  One recursion frame
 * assigns one position.  A palette of n distinct colours always works.
 */

#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

enum { MAX_N = 64, POLL_INTERVAL = 4096, MAX_SECONDS = 86400 };

enum result { NO_COLOURING, FOUND, TIMED_OUT, CLOCK_ERROR };

struct search {
    uint64_t colour[MAX_N];
    uint64_t domain[MAX_N];
    struct timespec start;
    int seconds;
    unsigned until_poll;
};

static uint64_t palette(int count)
{
    return count == MAX_N ? UINT64_MAX : (UINT64_C(1) << count) - 1;
}

static uint64_t first_colour(uint64_t choices)
{
    /* All callers pass a nonzero mask. */
    return UINT64_C(1) << __builtin_ctzll(choices);
}

static enum result check_time(const struct search *state)
{
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) {
        return CLOCK_ERROR;
    }
    double elapsed = (double)now.tv_sec - (double)state->start.tv_sec
                   + ((double)now.tv_nsec - (double)state->start.tv_nsec) * 1e-9;
    return elapsed >= (double)state->seconds ? TIMED_OUT : FOUND;
}

static void undo_domains(struct search *state, int x,
                         const uint64_t saved[], int count)
{
    for (int d = 1; d <= count; ++d) {
        state->domain[x + d] = saved[d - 1];
    }
}

static enum result assign(struct search *state, int n, int x,
                          uint64_t used, uint64_t colours)
{
    if (--state->until_poll == 0) {
        state->until_poll = POLL_INTERVAL;
        enum result time_status = check_time(state);
        if (time_status != FOUND) {
            return time_status;
        }
    }
    if (x == n) {
        return FOUND;
    }

    uint64_t unused = colours & ~used;
    uint64_t choices = state->domain[x] & (used | (unused ? first_colour(unused) : 0));
    int last_step = x / 2;
    if (last_step > n - 1 - x) {
        last_step = n - 1 - x;
    }

    /* The two bounds on d imply 3*d <= n-1. */
    uint64_t saved[MAX_N / 3];
    for (int d = 1; d <= last_step; ++d) {
        saved[d - 1] = state->domain[x + d];
    }

    while (choices != 0) {
        uint64_t bit = first_colour(choices);
        choices ^= bit;
        state->colour[x] = bit;

        int d = 1;
        for (; d <= last_step; ++d) {
            uint64_t a = state->colour[x - 2*d];
            uint64_t b = state->colour[x - d];
            uint64_t next = saved[d - 1];
            if (a == b && b == bit) {
                break;
            }
            if (a == b || a == bit || b == bit) {
                next &= ~(a | b | bit);
                if (next == 0) {
                    break;
                }
            }
            state->domain[x + d] = next;
        }

        if (d > last_step) {
            enum result answer = assign(state, n, x + 1, used | bit, colours);
            if (answer != NO_COLOURING) {
                return answer;
            }
        }
        undo_domains(state, x, saved, d - 1);
    }
    return NO_COLOURING;
}

static int extend_witness(struct search *state, int n, uint64_t choices)
{
    int x = n - 1;
    for (int d = 1; d <= x / 3; ++d) {
        uint64_t a = state->colour[x - 3*d];
        uint64_t b = state->colour[x - 2*d];
        uint64_t c = state->colour[x - d];
        if (a == b && b == c) {
            return 0;
        }
        if (a == b || a == c || b == c) {
            choices &= ~(a | b | c);
        }
    }
    if (choices == 0) {
        return 0;
    }
    state->colour[x] = first_colour(choices);
    return 1;
}

static int read_bounded(const char *arg, int upper, int *value)
{
    if (*arg < '0' || *arg > '9') {
        return 0;
    }
    char *end;
    errno = 0;
    long number = strtol(arg, &end, 10);
    if (errno == ERANGE || *end != '\0' || number < 1 || number > upper) {
        return 0;
    }
    *value = (int)number;
    return 1;
}

static enum result find_minimum(struct search *state, int n, int *count)
{
    if (clock_gettime(CLOCK_MONOTONIC, &state->start) != 0) {
        return CLOCK_ERROR;
    }
    if (extend_witness(state, n, palette(*count))) {
        return FOUND;
    }
    state->until_poll = 1;
    for (; *count <= n; ++*count) {
        uint64_t colours = palette(*count);
        for (int x = 0; x < n; ++x) {
            state->domain[x] = colours;
        }
        enum result answer = assign(state, n, 0, 0, colours);
        if (answer != NO_COLOURING) {
            return answer;
        }
    }
    return NO_COLOURING;
}

static int valid_witness(const struct search *state, int n, uint64_t colours)
{
    for (int x = 0; x < n; ++x) {
        uint64_t bit = state->colour[x];
        if ((bit & colours) != bit || __builtin_popcountll(bit) != 1) {
            return 0;
        }
    }
    for (int d = 1; d <= (n - 1) / 3; ++d) {
        for (int a = 0; a + 3*d < n; ++a) {
            uint64_t used = state->colour[a] | state->colour[a + d]
                          | state->colour[a + 2*d] | state->colour[a + 3*d];
            if (__builtin_popcountll(used) < 3) {
                return 0;
            }
        }
    }
    return 1;
}

int main(int argc, char **argv)
{
    int nmax;
    struct search state = { .seconds = 60 };
    if (argc < 2 || argc > 3 || !read_bounded(argv[1], MAX_N, &nmax) ||
        (argc == 3 && !read_bounded(argv[2], MAX_SECONDS, &state.seconds))) {
        fprintf(stderr, "Usage: 402186_01 NMAX (1..%d) [SECONDS_PER_TERM (1..%d)]\n",
                MAX_N, MAX_SECONDS);
        return EXIT_FAILURE;
    }

    int count = 1;
    for (int n = 1; n <= nmax; ++n) {
        enum result answer = find_minimum(&state, n, &count);
        if (answer == TIMED_OUT) {
            fprintf(stderr, "n=%d: unknown (%d s limit while testing %d colours)\n",
                    n, state.seconds, count);
            return 2;
        }
        if (answer != FOUND) {
            fprintf(stderr, "n=%d: %s\n", n, answer == CLOCK_ERROR
                    ? "monotonic clock failed" : "search failed to find a colouring");
            return EXIT_FAILURE;
        }
        if (!valid_witness(&state, n, palette(count))) {
            fprintf(stderr, "n=%d: invalid colouring produced by search\n", n);
            return EXIT_FAILURE;
        }
        if (printf("%d %d\n", n, count) < 0 || fflush(stdout) == EOF) {
            fputs("Could not write term to standard output.\n", stderr);
            return EXIT_FAILURE;
        }
        fprintf(stderr, "N=%d: h=%d, colouring:", n, count);
        for (int x = 0; x < n; ++x) {
            fprintf(stderr, " %d", 1 + __builtin_ctzll(state.colour[x]));
        }
        fputc('\n', stderr);
    }
    return EXIT_SUCCESS;
}
