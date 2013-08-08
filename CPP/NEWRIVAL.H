#ifdef _DEBUG
	#define TESTING
#endif

//#define TESTING

#include <fstream>
#include <iostream>

#define NORANDOM
#define LOG_COMMUNICATIONS
//#define LOG_VERBOSE_COMMUNICATIONS
//#define VERBOSE_LOGGING
#define COMMAND_ENDL "\n"
#define STRING_SIZE 5000
#define MAX_COMMAND_WORDS 1000

//#define STALEHASHTABLEBEFOREMOVE

#define DEFAULT_ASPIRE_WINDOW 200

#define DEFAULT_USE_NULL_MOVE 1
#define DEFAULT_NULL_MOVE_STOP_MATERIAL 2
#define DEFAULT_NULL_MOVE_REDUCE_DEPTH 3

#define DEFAULT_USE_CHECK_EXTENSIONS 1
#define DEFAULT_USE_FAIL_HIGH_REDUCTIONS 0
#define DEFAULT_USE_PAWNPUSH_EXTENSIONS 0
#define DEFAULT_USE_HISTORY 1
#define DEFAULT_USE_PIECE_SQUARE_VALUES_IN_ORDERING false
#define DEFAULT_STOP_PST_AT_MATERIAL 15000

#define DEFAULT_RANDOM_MOVE_ORDER 0

#define DEFAULT_MAX_EXTENSIONS 25

using namespace std;

#define MAXFILENAMELENGTH 300
#define MAXFEN 100

#define LEVEL 0
#define TIMEPERMOVE 1
#define CHAMPIONSHIP 2
#define BASEINCREMENT 3
#define INFINITETIME 4

#ifndef _newrivalh
#define _newrivalh

struct TOpeningPosition
{
#ifdef DYNAMICFEN
	char* Fen;
#else
	char Fen[MAXFEN];
#endif
	int WhiteWins;
	int BlackWins;
	int Draws;
   int FenLen;
};

#endif
