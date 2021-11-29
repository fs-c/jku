#include <stdio.h>
#include <stdlib.h>

#include "game-io.h"

// Global state.
int picked_suitcase = -1;

const int suitcases_length = 26;
// Cents. This will be modified to reflect eliminations during the game.
long suitcases[] = {
    1, 100, 500, 1000, 2500, 5000, 7500, 10000, 20000, 30000, 40000, 50000,
    75000, 100000, 500000, 1000000, 2500000, 5000000, 7500000, 10000000,
    20000000, 30000000, 40000000, 50000000, 75000000, 100000000
};

const int eliminated_cases_length = 5;
const int eliminated_cases[] = { 6, 5, 4, 3, 2 };

typedef struct { long euro; long cent; } currency_t;

// Convert a raw currency value (in cents) into euros and cents.
currency_t to_currency(long value) {
    currency_t cur;

    cur.euro = value / 100;
    cur.cent = value - (cur.euro * 100);

    return cur;
}

// Prints all suitcases, excluding eliminated ones and the picked one.
void print_suitcases() {
    for (int i = 0; i < suitcases_length; i++) {
        if (suitcases[i] && i != picked_suitcase) {
            printf("[%d]", i + 1);
        }
    }

    putc('\n', stdout);
}

// Shuffle the first n elements of the given array randomly.
void randomize(long *array, size_t n) {
    if (n <= 1) {
        return;
    }

    for (size_t i = 0; i < n - 1; i++) {
        // Randomly determine a new index.
        size_t j = i + rand() / (RAND_MAX / (n - i) + 1);

        // Switch elements at new and old index.
        long t = array[j];
        array[j] = array[i];
        array[i] = t;
    }
}

// Prompt player to choose a suitcase in the context of a given message. Retry 
// until a valid response is given.
size_t player_choose_suitcase(const char *message) {
    unsigned int pick;

    while (true) {
        fputs(message, stdout);

        if (!askPlayerForNumber(&pick)) {
            fputs(input_invalid, stdout);

            continue;
        }

        if (pick <= 0 || pick > suitcases_length) {
            fputs(input_out_of_range, stdout);

            continue;
        }

        if ((pick - 1) == picked_suitcase || !suitcases[pick - 1]) {
            fputs(suitcase_not_availalbe, stdout);

            continue;
        }

        return pick;
    }
}

// Promt player to answer yes/no to a given question. Retry until a valid response 
// is given.
bool player_prompt_yn(const char *message) {
    while (true) {
        fputs(message, stdout);

        yes_no_retry_t result = askPlayerYesNo();

        if (result == Yes) {
            return 1;
        } else if (result == No) {
            return 0;
        } else if (result == Retry) {
            fputs(input_invalid, stdout);
        }
    }
}

// Get the places of a number. I. e. 7 for 1276435.
int get_places(long num) {
    // Number of places.
    int p = 1;

    // Keep deviding by 10 (and incrementing the places) as long as possible.
    while (num > 9) {
        num /= 10;
        p++;
    }

    return p;
}

// Calculate the current bank offer based on the game state.
long get_bank_offer(int round) {
    // Total value of the remaining suitcases. (Incl. pick.)
    long total_value = 0;
    // Number of remaining suitcases. (Incl. pick.)
    int remaining = 0;
    for (int i = 0; i < suitcases_length; i++) {
        total_value += suitcases[i];

        if (suitcases[i]) {
            remaining++;
        }
    }

    long offer = (total_value / remaining) * (round + 1) / 10;

    // Ghetto rounding

    int places = get_places(offer);

    for (int i = 0; i < places - 3; i++) {
        offer /= 10;
    }

    if (offer % ((offer / 10) * 10)) {
        offer = ((offer / 10) + 1) * 10;
    }

    for (int i = 0; i < places - 3; i++) {
        offer *= 10;
    }

    return offer;
}

int main (int argc, const char *argv[]) {
    bool should_randomize = false;

    if (argc == 2) {
        // Very scalable, stonks
        if (argv[1][0] != '-' || argv[1][1] != 'r') {
            printf(argument_invalid, argv[1]);

            return EXIT_FAILURE;
        }

        should_randomize = true;
    } else if (argc > 3) {
        fputs(arguments_too_many, stdout);

        return EXIT_FAILURE;
    }

    if (should_randomize) {
        fputs(suffeling_suitcase_contents, stdout);

        randomize(suitcases, suitcases_length);
    }

    print_suitcases();

    picked_suitcase = player_choose_suitcase(prompt_pick_prize) - 1;

    printf(confirm_prize_suitcase, picked_suitcase + 1);

    for (int round = 0; round < 9; round++) {
        // Number of cases to eliminate in the current round
        int e = round >= eliminated_cases_length ? 1 : eliminated_cases[round];

        print_suitcases();
        printf(intro_round, round + 1, e);

        for (int i = 0; i < e; i++) {
            int p = player_choose_suitcase(prompt_pick_to_eliminate);

            long *v = &suitcases[p - 1];
            currency_t cur = to_currency(*v);

            printf(confirm_pick_to_eliminate, p, cur.euro, cur.cent);

            *v = 0;
        }

        currency_t bank_offer = to_currency(get_bank_offer(round));

        printf(intro_bank_offer, bank_offer.euro, bank_offer.cent);

        if (player_prompt_yn(prompt_bank_offer)) {
            printf(confirm_bank_offer_gameover_early, bank_offer.euro,
                bank_offer.cent);

            return EXIT_SUCCESS;
        }
    }

    int remaining = -1;
    for (int i = 0; i < suitcases_length; i++) {
        if (suitcases[i] && i != picked_suitcase) {
            remaining = i;
        }
    }

    printf(intro_switch_suitcase, picked_suitcase + 1, remaining + 1);

    if (player_prompt_yn(prompt_switch_suitcase)) {
        printf(confirm_switch_suitcase, picked_suitcase + 1, remaining + 1);

        picked_suitcase = remaining;
    }

    currency_t prize = to_currency(suitcases[picked_suitcase]);

    printf(game_over_full_game, picked_suitcase + 1, prize.euro, prize.cent);

    return EXIT_SUCCESS;
}
