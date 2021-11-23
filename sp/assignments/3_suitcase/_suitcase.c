#include <stdio.h>
#include <stdlib.h>

#include "game-io.h"

// Shuffle the first n elements of the given array randomly.
void shuffle(int *array, size_t n) {
    if (n <= 1) {
        return;
    }

    for (size_t i = 0; i < n - 1; i++) {
        size_t j = i + rand() / (RAND_MAX / (n - i) + 1);
        int t = array[j];
        array[j] = array[i];
        array[i] = t;
    }
}

const int suitcases_length = 26;
double suitcases[] = { 0.1, 1, 5, 10, 25, 50, 75, 100, 200, 300, 400, 500, 750, 1000, 5000, 10000, 25000, 50000, 75000, 100000, 200000, 300000, 400000, 500000, 750000, 1000000 };

const int eliminated_cases_length = 6;
const int eliminated_cases[] = { 6, 5, 4, 3, 2, 1 };

int pick_suitcase() {
    int pick;
    printf(prompt_pick_prize);
    while (!askPlayerForNumber(&pick)) {
        printf(prompt_pick_prize);
    }

    return pick;
}

int get_bank_offer() {
    int sval = 0;
    for (int i = 0; i < suitcases_length; i++) {
        sval += suitcases[i]
    }


}

int main (int argc, const char *argv[]) {
    bool randomize = false;

    if (argc == 3) {
        if (argv[3][0] != '-' && argv[3][0] != 'r') {
            printf(argument_invalid, argv[3]);
        }

        randomize = true;
    } else if (argc > 3) {
        printf(arguments_too_many);

        return EXIT_FAILURE;
    }

    if (randomize) {
        printf(suffeling_suitcase_contents);

        shuffle(suitcases, suitcases_length);
    }

    int picked_suitcase = pick_suitcase();
    int round = 1;

    // Main game loop
    while (true) {
        int eliminations = round > eliminated_cases_length ? 1 : eliminated_cases[round];

        printf(intro_round, round, eliminations);

        int i = 0;
        while (i < eliminations) {
            printf(prompt_pick_to_eliminate);

            int elim_pick;
            while (!askPlayerForNumber(&elim_pick));

            if (elim_pick <= 0 || elim_pick > suitcases_length) {
                printf(input_out_of_range);

                continue;
            }

            if (elim_pick == picked_suitcase || suitcases[elim_pick - 1] == 0) {
                printf(suitcase_not_availalbe);

                continue;
            }

            printf(confirm_pick_to_eliminate, elim_pick - 1, (long)suitcases[elim_pick - 1], (long)(suitcases[elim_pick - 1] * 100) % ((long)suitcases[elim_pick - 1] * 100));
            suitcases[elim_pick - 1] = 0;

            i++;
        }

        int bank_offer = get_back_offer();
    }

    return EXIT_SUCCESS;
}

