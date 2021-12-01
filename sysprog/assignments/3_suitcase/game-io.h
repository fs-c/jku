#ifndef GAME_IO_H
#define GAME_IO_H

#include <stdbool.h>
#include <stdint.h>

/*
 * The return value type of askPlayerYesNo()
 */
typedef enum yes_no_retry {
    Yes, No, Retry
} yes_no_retry_t;

/*
 * Expects a line of input from the player, terminated by pressing ENTER.
 * If the input line is "y\n" Yes is returned.
 * If the input line is "n\n" No is returned.
 * Otherwise Retry is returned.
 */
yes_no_retry_t askPlayerYesNo();

/*
 * Expects a line of input from the player, terminated by pressing ENTER.
 * If the input contains a number, the number argument
 * is set to that number and true is returned.
 * If the input cannot be parsed as a number, false is returned.
 */
bool askPlayerForNumber(unsigned int* number);

/*
 * Command line output strings.
 */
static const char arguments_too_many[] = "Too many arguments.\n";
static const char argument_invalid[] = "Invalid argument: '%s'.\n";
static const char input_invalid[] = "Invalid selection.\n";
static const char input_out_of_range[] = "Number out of range.\n";
static const char suffeling_suitcase_contents[] = "Shuffeling contents between suitcases.\n";
static const char prompt_pick_prize[] = "Pick the suitcase with your prize (1-26):\n";
static const char confirm_prize_suitcase[] = "You picked suitcase %d.\n";
static const char intro_round[] = "Round %d (eliminate %d):\n";
static const char prompt_pick_to_eliminate[] = "Pick a suitcase to elimiiate from the game:\n";
static const char confirm_pick_to_eliminate[] = "Eliminated case %d. Contains %ld.%02ld\n";
static const char suitcase_not_availalbe[] = "Suitcase no longer avilable to pick.\n";
static const char intro_bank_offer[] = "The bank offers you %ld.%02ld to exit the game.\n";
static const char prompt_bank_offer[] = "Do you accept the offer?[y/n]\n";
static const char confirm_bank_offer_gameover_early[] = "Ending game early with %ld.%02ld.\n";
static const char intro_switch_suitcase[] = "You have picked suitcase %d, suitcase %d is the last one remaining.\n";
static const char prompt_switch_suitcase[] = "Do you want to switch suitcases?[y/n]\n";
static const char confirm_switch_suitcase[] = "Switching from suitcase %d to %d.";
static const char game_over_full_game[] = "Game over.\nOpening suitcase %d.\nYou win %ld.%02ld.\n";

#endif

