#ifndef _SEARCHER_H
#define _SEARCHER_H
#include "chessbrd.h"
#include "searchdf.h"
#include "newadd.h"
#include "assert.h"
using std::string;

#define POLL_TICKS 500000

//#define NEWKINGSAFETY

#define USINGALLMOVESINQUIESCE
#define USINGALLCHECKINGMOVESINQUIESCE

#define MAXCHECKEXTENDSINQUIESCE 0
#define MAX_CHECKING_MOVES_ONE_PLY_IN_QUIESCE 10

//#define USEHASHINQUIESCE
#define USE_TWO_HASH_TABLES
#define EXTENDPLY 1

#define VERIFIEDNULLMOVE
//#define FUTILITYPRUNING
#define FUTILITYMARGIN1 300
#define FUTILITYMARGIN2 600

#define COUNTNODESINQUIESCE
#define COUNTNODESINMINIMAX

#define TESTING_CHECKING_MOVE_DETECTION
//#define LONG_CHECKING_IN_QUIESCE

//#define USEPIECESQUARETABLESINEVAL
#define PIECESQUAREEVALMULTIPLIER 1
#define FAILHIGHERROR 100
//#define NEWFAILHIGHCODE

// Pawn in eval = 1000, Pawn in search = 100
#define EVALUATION_PIECEVALUE_MULTIPLIER 10

#define LOWEVAL -32000
#define HIGHEVAL 32000

#define BASECAPTURE 2000L
#define HASHMOVEBONUS 6002L
#define PVMOVEBONUS 0
#define LASTMOVEPIECEBONUS 1000L //5001L
#define HISTORYSCOREMAX 3000
#define MAXHISTORYDEPTH 19

#define WRITE_PV_MINIMUM_DEPTH 3
#define WRITE_CURRENT_MOVE_MINIMUM_DEPTH 3

#define PAWNVALUE 1000
#define KNIGHTVALUE 3250
#define BISHOPVALUE 3250
#define ROOKVALUE 5000
#define QUEENVALUE 9000
#define BISHOPPAIRBONUS 500

#define DOUBLEDPAWNS 400  // Penalty for each extra pawn on file
#define ISOLATEDPAWN 75
#define PASSEDPAWN 150 // per rank
#define PASSEDPAWNHOME 500 // per rank
#define PAWNADVANCEMULTIPLIER 1 // Multiply regular advance by this when not in end game
#define PAWNADVANCEENDGAME 1 // Multiply regular advance by this when in end game
#define BACKWARDPAWNPENALTY 200

#define DOUBLEDFILEROOKS 160 // for the pair
#define DOUBLEDRANKROOKS 100 // for the pair
#define ROOKONOPENFILE 150
#define ROOKONSEMIOPENFILE 45
#define ROOKSEVENTHRANK 125
#define QUEENOUTEARLY 150
#define NOCASTLEPOSSIBLE KINGCASTLENOPOSSIBLE+QUEENCASTLENOPOSSIBLE
#define RATIOBONUS 10 // Multiply by number of friendly pawns (>3 ? 3) and piece difference
#define ROOKFILEMOBILITY 45 // per square
#define ROOKRANKMOBILITY 25 // per square
#define QUEENMOBILITY 45 // per square
#define BISHOPMOBILITY 45 // per square
#define ENDGAMEPIECES QUEENVALUE + KNIGHTVALUE
#define OPENINGPIECES QUEENVALUE + (ROOKVALUE * 2) + KNIGHTVALUE + BISHOPVALUE
#define UNDEVELOPEDMINOR 35
#define CENTRALOCCUPATION 150 // e.g. rook vs knight = 2*MOVEKINGNEAR*(14-(rank distance + file distance))
#define MOVEKINGNEAR 0 // multiplied by [0 to 7]
#define OPPOSITION2 50
#define OPPOSITION4 30
#define OPPOSITION6 10
#define MINORKINGSAFETYUNIT 25
#define KINGCENTRE 10
#define KINGSAFETYUNIT 60
#define KINGSAFETYVERYWEAK KINGSAFETYUNIT
#define KINGSAFETYWEAK KINGSAFETYUNIT*2
#define KINGSAFETYQUITEWEAK KINGSAFETYUNIT*3
#define KINGSAFETYQUITESTRONG KINGSAFETYUNIT*4
#define KINGSAFETYSTRONG KINGSAFETYUNIT*5
#define KINGSAFETYVERYSTRONG KINGSAFETYUNIT*6

#define KINGSAFETY_HOLEINDEFENCE 25
#define KINGSAFETY_PAWNMISSING 50
#define KINGSAFETY_NOTYETCASTLED 12
#define KINGSAFETY_NOTONBACKRANK 25
#define KINGCASTLENOPOSSIBLE 10
#define QUEENCASTLENOPOSSIBLE 6

#define UNKNOWN 0
#define NULLMOVE 1
#define PAWNPUSH 2
#define ONLYMOVE 4
#define PUTINCHECK 8
#define CAPTURE 16

const int Valid[110]=
	{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 1, 1, 1, 1, 1, 1, 1, 1, 0,
	  0, 1, 1, 1, 1, 1, 1, 1, 1, 0,
	  0, 1, 1, 1, 1, 1, 1, 1, 1, 0,
	  0, 1, 1, 1, 1, 1, 1, 1, 1, 0,
	  0, 1, 1, 1, 1, 1, 1, 1, 1, 0,
	  0, 1, 1, 1, 1, 1, 1, 1, 1, 0,
	  0, 1, 1, 1, 1, 1, 1, 1, 1, 0,
	  0, 1, 1, 1, 1, 1, 1, 1, 1, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0 };

// TypeIndexes[WP] = Index to position for number of white pawns
// TypeIndexes[BQ] = Index to position for number of black queens
const int TypeIndexes[107]=
	{ 0,
	  WHITEPAWNS,
	  WHITEKNIGHTS,
	  WHITEBISHOPS,
	  WHITEROOKS,
	  WHITEQUEENS,
	  WHITEKINGS,
	  0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  BLACKPAWNS,
	  BLACKKNIGHTS,
	  BLACKBISHOPS,
	  BLACKROOKS,
	  BLACKQUEENS,
	  BLACKKINGS };


const int A1H8Diagonal[89]=
	{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 1 };

const int A8H1Diagonal[89]=
	{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
	  0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
	  0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
	  0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
	  0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
	  0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
	  0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
	  0, 1, 0, 0, 0, 0, 0, 0, 0 };

const int A2G8Diagonal[89]=
	{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0 };

const int A7G1Diagonal[89]=
	{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
	  0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
	  0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
	  0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
	  0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
	  0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
	  0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0 };

const int B1H7Diagonal[89]=
	{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 1, 0 };

const int B8H2Diagonal[89]=
	{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
	  0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
	  0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
	  0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
	  0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
	  0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
	  0, 0, 1, 0, 0, 0, 0, 0, 0 };

const int WhitePawnAdvance[88]=
	{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 5*PAWNADVANCEMULTIPLIER, 10*PAWNADVANCEMULTIPLIER, 15*PAWNADVANCEMULTIPLIER, 20*PAWNADVANCEMULTIPLIER, 25*PAWNADVANCEMULTIPLIER, 0, 0,
	  0, 0, 0, 5*PAWNADVANCEMULTIPLIER, 10*PAWNADVANCEMULTIPLIER, 30*PAWNADVANCEMULTIPLIER, 40*PAWNADVANCEMULTIPLIER, 50*PAWNADVANCEMULTIPLIER, 0, 0,
	  0, 0, 0, 20*PAWNADVANCEMULTIPLIER, 30*PAWNADVANCEMULTIPLIER, 90*PAWNADVANCEMULTIPLIER, 110*PAWNADVANCEMULTIPLIER, 135*PAWNADVANCEMULTIPLIER, 0, 0,
	  0, 0, 0, 35*PAWNADVANCEMULTIPLIER, 80*PAWNADVANCEMULTIPLIER, 120*PAWNADVANCEMULTIPLIER, 150*PAWNADVANCEMULTIPLIER, 180*PAWNADVANCEMULTIPLIER, 0, 0,
	  0, 0, 0, 35*PAWNADVANCEMULTIPLIER, 80*PAWNADVANCEMULTIPLIER, 120*PAWNADVANCEMULTIPLIER, 150*PAWNADVANCEMULTIPLIER, 180*PAWNADVANCEMULTIPLIER, 0, 0,
	  0, 0, 0, 20*PAWNADVANCEMULTIPLIER, 30*PAWNADVANCEMULTIPLIER, 90*PAWNADVANCEMULTIPLIER, 110*PAWNADVANCEMULTIPLIER, 135*PAWNADVANCEMULTIPLIER, 0, 0,
	  0, 0, 0, 5*PAWNADVANCEMULTIPLIER, 10*PAWNADVANCEMULTIPLIER, 30*PAWNADVANCEMULTIPLIER, 40*PAWNADVANCEMULTIPLIER, 50*PAWNADVANCEMULTIPLIER, 0, 0,
	  0, 0, 0, 5*PAWNADVANCEMULTIPLIER, 10*PAWNADVANCEMULTIPLIER, 15*PAWNADVANCEMULTIPLIER, 20*PAWNADVANCEMULTIPLIER, 25*PAWNADVANCEMULTIPLIER };

const int WhiteSeventhRank[89]=
	{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 1, 0 };

const int BlackSeventhRank[89]=
	{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 1, 0, 0, 0, 0, 0, 0 };

const int WhiteBackRank[89]=
	{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 1, 0, 0, 0, 0, 0, 0, 0 };

const int BlackBackRank[89]=
	{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 1 };

const int Quadrant[89]=
	{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 1, 1, 1, 1, 2, 2, 2, 2, 0,
	  0, 1, 1, 1, 1, 2, 2, 2, 2, 0,
	  0, 1, 1, 1, 1, 2, 2, 2, 2, 0,
	  0, 1, 1, 1, 1, 2, 2, 2, 2, 0,
	  0, 4, 4, 4, 4, 3, 3, 3, 3, 0,
	  0, 4, 4, 4, 4, 3, 3, 3, 3, 0,
	  0, 4, 4, 4, 4, 3, 3, 3, 3, 0,
	  0, 4, 4, 4, 4, 3, 3, 3, 3 };

const int CornerSquare[89]=
	{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 1, 1, 0, 0, 0, 0, 1, 1, 0,
	  0, 1, 1, 0, 0, 0, 0, 1, 1, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 1, 1, 0, 0, 0, 0, 1, 1, 0,
	  0, 1, 1, 0, 0, 0, 0, 1, 1 };

const int CentreKing[89]=
	{ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	  0, 0, 1, 1, 1, 1, 1, 1, 0, 0,
	  0, 0, 1, 5, 5, 5, 5, 1, 0, 0,
	  0, 0, 1, 5, 10, 10, 5, 1, 0, 0,
	  0, 0, 1, 5, 10, 10, 5, 1, 0, 0,
	  0, 0, 1, 5, 5, 5, 5, 1, 0, 0,
	  0, 0, 1, 1, 1, 1, 1, 1, 0, 0,
	  0, 0, 0, 0, 0, 0, 0, 0, 0 };

const int knightcontrol[89]={
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, -128,-96, -164, -132, -132, -164, -96, -128, 0,
	0, -96, -64, -32,  0,  0, -32, -64, -96, 0,
	0, -64, -32,  32,  32,  32,  32, -32, -64, 0,
	0, -32,  0,  32,  32,  32,  32,  0, -32, 0,
	0, -32,  0,  32,  32,  32,  32,  0, -32, 0,
	0, -64, -32,  32,  32,  32,  32, -32, -64, 0,
	0, -96, -64, -32,  0,  0, -32, -64, -96, 0,
	0, -128,-96, -164, -132, -132, -164, -96, -128
};

const int KnightMoveScores[89]={
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 5, 0, 10, 10, 10, 10, 0, 0,
	0, 5, 20, 26, 22, 23, 28, 24, 10, 0,
	0, 15, 20, 26, 28, 36, 40, 26, 20, 0,
	0, 15, 23, 30, 30, 40, 50, 26, 20, 0,
	0, 15, 20, 30, 30, 40, 50, 26, 20, 0,
	0, 15, 20, 26, 22, 23, 28, 24, 10, 0,
	0, 0, 20, 26, 22, 23, 28, 24, 10, 0,
	0, 0, 5, 0, 10, 10, 10, 10, 0
};

const int WhitePawnPieceSquareTable[89] = {
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 2, 4, 4, 6, 10, 10, 0, 0,  // a1..a8
	0, 0, 3, 6, 7, 11, 15, 15, 0, 0,
	0, 4, 12, 18, 18, 24, 24, 0, 0,
	0, 0, 12, 25, 27, 32, 32, 0, 0,
	0, 0, 12, 25, 27, 32, 32, 0, 0,
	0, 0, 4, 4, 16, 16, 24, 24, 0, 0,
	0, 0, 3, 6, 7, 11, 15, 15, 0, 0,
	0, 0, 2, 4, 4, 6, 10, 10, 0
};

const int BlackPawnPieceSquareTable[89] = {
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 10, 10, 6, 4, 4, 2, 0, 0,
	0, 0, 15, 15, 11, 7, 6, 3, 0, 0,
	0, 0, 24, 24, 18, 18, 12, 4, 0, 0,
	0, 0, 32, 32, 27, 25, 12, 0, 0, 0,
	0, 32, 32, 27, 25, 12, 0, 0, 0,
	0, 24, 24, 16, 16, 4, 4, 0, 0,
	0, 15, 15, 11, 7, 6, 3, 0, 0,
	0, 10, 10, 6, 4, 4, 2, 0,
};

const int WhiteKnightPieceSquareTable[89] = {
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, -7, 2, 6, 8, 8, 6, 2, -7, 0,
	0, -3, 6, 14, 18, 18, 14, 6, -3, 0,
	0, 1, 14, 22, 26, 30, 28, 14, 1, 0,
	0, 3, 20, 26, 30, 32, 32, 20, 3, 0,
	0, 3, 20, 26, 30, 32, 32, 20, 3, 0,
	0, 1, 14, 22, 26, 30, 28, 14, 1, 0,
	0, -3, 6, 14, 18, 18, 14, 6, -3, 0,
	0, -7, 2, 6, 8, 8, 6, 2, -7
};

const int BlackKnightPieceSquareTable[89] = {
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, -7, 2, 6, 8, 8, 6, 2, -7, 0,
	0, -3, 6, 14, 18, 18, 14, 6, -3, 0,
	0, 1, 14, 22, 26, 30, 28, 14, 1, 0,
	0, 3, 20, 26, 30, 32, 32, 20, 3, 0,
	0, 3, 20, 26, 30, 32, 32, 20, 3, 0,
	0, 1, 14, 22, 26, 30, 28, 14, 1, 0,
	0, -3, 6, 14, 18, 18, 14, 6, -3, 0,
	0, -7, 2, 6, 8, 8, 6, 2, -7
};

const int WhiteBishopPieceSquareTable[89] = {
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 16, 26, 26, 16, 16, 16, 16, 16, 0,
	0, 16, 29, 28, 26, 26, 28, 29, 16, 0,
	0, 16, 31, 32, 32, 32, 32, 31, 16, 0,
	0, 16, 31, 32, 32, 32, 32, 31, 16, 0,
	0, 16, 31, 32, 32, 32, 32, 31, 16, 0,
	0, 16, 31, 32, 32, 32, 32, 31, 16, 0,
	0, 16, 29, 28, 26, 26, 28, 29, 16, 0,
	0, 16, 26, 26, 16, 16, 16, 16, 16
};

const int BlackBishopPieceSquareTable[89] = {
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 16, 26, 26, 16, 16, 16, 16, 16, 0,
	0, 16, 29, 28, 26, 26, 28, 29, 16, 0,
	0, 16, 31, 32, 32, 32, 32, 31, 16, 0,
	0, 16, 31, 32, 32, 32, 32, 31, 16, 0,
	0, 16, 31, 32, 32, 32, 32, 31, 16, 0,
	0, 16, 31, 32, 32, 32, 32, 31, 16, 0,
	0, 16, 29, 28, 26, 26, 28, 29, 16, 0,
	0, 16, 26, 26, 16, 16, 16, 16, 16
};

const int WhiteRookPieceSquareTable[89] = {
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, -2, -2, -2, -2, -2, 10, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 10, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 10, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 10, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 10, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 10, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 10, 0, 0,
	0, -2, -2, -2, -2, -2, 10, 0
};

const int BlackRookPieceSquareTable[89] = {
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 10, -2, -2, -2, -2, 0, 0,
	0, 0, 10, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 10, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 10, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 10, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 10, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 10, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 10, -2, -2, -2, -2, 0
};

const int WhiteQueenPieceSquareTable[89] = {
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, -2, 0, 0, 0, 0, -2, -2, -2, 0,
	0, -2, 0, 1, 0, 0, -2, -2, -2, 0,
	0, -2, 1, 1, 0, 0, 0, 0, 0, 0, 
	0, 0, 1, 1, 2, 2, 0, 0, 0, 0,
	0, 0, 1, 1, 2, 2, 0, 0, 0, 0,
	0, -2, 0, 0, 0, 0, 0, 0, 0, 0,
	0, -2, 0, 0, 0, 0, 0, 0, 0, 0,
	0, -2, 0, 0, 0, 0, 0, 0, 0
};

const int BlackQueenPieceSquareTable[89] = {
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, -2, -2, -2, 0, 0, 0, 0, -2, 0,
	0, -2, -2, -2, 0, 0, 1, 0, -2, 0,
	0, 0, 0, 0, 0, 0, 1, 1, -2, 0,
	0, 0, 0, 0, 2, 2, 1, 1, 0, 0,
	0, 0, 0, 0, 2, 2, 1, 1, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0, -2, 0,
	0, 0, 0, 0, 0, 0, 0, 0, -2, 0,
	0, 0, 0, 0, 0, 0, 0, 0, -2
};

const int WhiteKingPieceSquareTable[89] = {
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 3, -5, -7, -20, -20, -20, -20, -20, 0,
	0, 3, -5, -15, -20, -20, -20, -20, -20, 0,
	0, 8, -12, -15, -20, -20, -20, -20, -20, 0,
	0, -12, -12, -15, -20, -20, -20, -20, -20, 0,
	0, -8, -12, -15, -20, -20, -20, -20, -20, 0,
	0, -12, -12, -15, -20, -20, -20, -20, -20, 0,
	0, 10, -5, -15, -20, -20, -20, -20, -20, 0,
	0, 5, -5, -7, -20, -20, -20, -20, -20
};

const int BlackKingPieceSquareTable[89] = {
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, -20, -20, -20, -20, -20, -7, -5, 3, 0,
	0, -20, -20, -20, -20, -20, -15, -5, 3, 0,
	0, -20, -20, -20, -20, -20, -15, -12, 8, 0,
	0, -20, -20, -20, -20, -20, -15, -12, -12, 0,
	0, -20, -20, -20, -20, -20, -15, -12, -8, 0,
	0, -20, -20, -20, -20, -20, -15, -12, -12, 0,
	0, -20, -20, -20, -20, -20, -15, -5, 10, 0,
	0, -20, -20, -20, -20, -20, -7, -5, 5
};

#define MOVEARRAYMAX 200
#define SATISFACTION 50
#define MINIMALWINDOW
#define HASHTABLE

#define INCREASECONVERGER 15
#define MAXDEPTH 200

#define VALID 0
#define LBOUND 1
#define UBOUND 2

struct TPath
{
	TMove Move[MAXDEPTH];
	int Value;
	int Nodes;
	char Depth;
};

#define SIZEOFPATH 1612

typedef TMove TMoveArray[MOVEARRAYMAX];

class TSearcher {
	public:
		TSearcher(int);
      ~TSearcher();
		void SetMaxDepth(int);
		void SetMaxQuiesceDepth(int);
		void SetMaxExtensions(int);
		void SetAspireWindow(int);
		void SetUseHistory(int);
		void SetUseSingleReplyExtensions(int);
		void SetSearchMoves(string*);
		void SetPonderMode(int);
		void SetWhiteMillisRemaining(int);
		void SetBlackMillisRemaining(int);
		void SetWhiteIncrementMillis(int);
		void SetBlackIncrementMillis(int);
		void SetMovesToGoToTimeControl(int);
		void SetMaxSearchNodes(int);
		void SetisSearchingForMate(int);
		void SetMaxMoveTimeMillis(int);
		void SetNullMoveStopMaterial(int);
		void SetHashReadReduce(int);
		void SetHashWriteReduce(int);
		void SetUseNullMove(int);
		void SetUseFailHighReductions(int);
		void SetUseCheckExtensions(int);
		void SetUsePawnPushExtensions(int);
		void SetNullMoveReduceDepth(int);
		void SetUseMinimalWindow(int);
		int CalculateHashsize(int);
		int GetSearchStartTime();
		bool IsWhiteToMove();
		void SetContempt(int);
      void SetPrintPV(int);
		int Satisfied;
		virtual void SetInitialPosition(TChessBoard);
		void ClearHashTable();
		void StaleHashTable();
		void ClearHistory();
		void ExitWithoutMove();
		void ExitWithMove();
      int CalculateHashSize(int);
		void GeneratePieceValues();
		int GetCurrentPathNodes();
		TPath GetPrincipalPath();
		TPath Search();
		TPath SolveSearch();
		void TranslateMove(TMove, char*);
		void SetStopScore(int);
		void SetStopMove(TMove);
		void SetRandomMoveOrder(int);
		void WritePV(char*, char*);
		void SetSearchTimeMillis(int i);
		void SetMaxExtendedSearchTimeMillis(int i);
		void GetSimpleMoveString(TMove move, char* moveString);
		virtual int Evaluate();
	protected:
		void WriteCurrentMoveToGUI(int MoveNumber);
		void WritePrincipalPathToGUI();
		int VariantID;
		int MaxExtensions;
		int AspireWindow;
		int UseCheckExtensions;
		int UsePawnPushExtensions;
		int UseSingleReplyExtensions;
		int NullMoveReduceDepth;
		int MinimumMate;
		int LastMoveNumber;
		int RootMaterial;
		int KingSafety(TPosition);
		int HashPower;
		int PrintPV;
		unsigned int NumberOfHashEntries;
		unsigned int NumberOfHashEntriesAlwaysReplace;
		int UseNullMove;
		bool UsePieceSquareValuesInOrdering;
		bool UseOpeningLibrary;
		int UseFailHighReductions;
		int Amount;
		int LoneKing(TPosition Position);
		//int LoneKingAgainstPawns(TPosition Position);
		void SetupTropism();
		void ShowPosition(TPosition Position);
		int PawnValues[8];
		int searchStartTime;
		int timeticker;
		char* OpeningLibraryFilename;
		int searchTimeMillis;
		int MaxExtendedSearchTimeMillis;
		TMove DrawMoves[25];
		TMove Ply1DrawMovesPly0[25];
		TMove Ply1DrawMovesPly1[25];
		int PieceValues[107];
		int PieceValuesDiv10[107];
		int QueenKingTropism[89][89];
		int BishopKingTropism[89][89];
		int KnightKingTropism[89][89];
		int RookKingTropism[89][89];
		int KingKingTropism[89][89];
		int TropismNear[89][89];
		int TropismFar[89][89];
		int KnightAttacks[89][89];
		int SameDiagonal[89][89];
		virtual int VerifyMove(TPosition, TMove);
		int PieceSquareValues[89][12];
		unsigned long LockPieceSquareValues[89][12];
		unsigned long History[89][89];
		THashMove* HashTable;
		THashMove* HashTableAlwaysReplace;
		virtual int IsCheck(TPosition);
		inline int ComputeHashKey(TPosition);
#ifdef LOCKCHECKINHASH
		LockStruct EncodePosition(TPosition Position);
#endif
		virtual int GetMoveList(TPosition, TMoveArray);
		virtual int GetCheckMoveListWithoutCaptures(TPosition, TMoveArray);
		int FirstPieceOnLineViaSquare(TPosition Position, int FromSquare, int MoveDir, int ViaSquare, int BlockSquare);
		bool IsAttacked(TPosition Position, int FromSquare, int MoveDir, int TargetSquare);
		bool IsDiscoveredCheck(TPosition Position, int VacatedSquare, int KingSquare, int BlockSquare);
		bool IsCheckingMove(TPosition Position, TMove& Move);
		bool IsCheckingMoveStandard(TPosition Position, TMove& Move);
		virtual int GetQuickMoveList(TPosition, TMoveArray);
		virtual int GetQuickMoveListWithChecks(TPosition, TMoveArray);
		virtual int MakeMove(TPosition, TMove&, TPosition);
		int MakeMoveQuick(TPosition, TMove&, TPosition);
		virtual int Evaluate(TPosition, int, int);
		virtual int FastEvaluate(TPosition, int, int);
		virtual int WinnerWhenNoMoves(TPosition);
		virtual void GetHashMoveDetails(TPosition, int& Height, int& Flag, TMove&, int& Value);
		virtual void StoreHashMoveDetails(TPosition, int, int, TMove, int);
		TPath PrincipalPath;
		int CurrentPathNodes;
		int DebugCounter;
		TMove CurrentDepthZeroMove;
		virtual int PreviousPosition(TMove);
		int ExitCode;
		TPosition StartPosition;
		TMoveArray Depth0Moves;
		int GetFile[89];
		int GetRank[89];
		TMove GlobalHashMove;
		TMove TempMove;
		int CurrentDepth;
		TMove LastMove[MAXDEPTH];
		int PathBoard[89];
		int UseHistory;
   	int RandomMoveOrder;
	private:
		TMove StopMove;
		int StopScore;
		int ValueGuess;
		int NullMoveStopMaterial;
		int HashReadReduce, HashWriteReduce;
		TPosition NewPosition[MAXDEPTH];
		TMoveArray Moves[MAXDEPTH];
		void Minimax(TPosition, int, int, int, TPath*, int, bool);
		void MinimaxZero(TPosition, unsigned int, int, int, TPath*, unsigned int);
		void Quiesce(TPosition, int, int, int, TPath*, int, int, int);
		int MaxDepth;
		int MaxQuiesceDepth;
		int FinalDepth;
		int FinalQuiesceDepth;
		int LowEval;
		int HighEval;
		int Depth0Amount;
		int Contempt, UseMinimalWindow;
		void ReOrderMoves(TMoveArray, int);
		int PIBest;
};
#endif

#define \
AlterLocationInformation    \
{ \
/* Get an index to the locations for the type of piece that is moving */\
	TypeIndex=TypeIndexes[*FromPiece]; \
/* Find moving piece in location array */   \
	PieceIndex=TypeIndex;                  \
	while (NewPosition[++PieceIndex]!=Move.From); \
/* if this is a pawn promotion then delete location and add new piece at Move.To */ \
	if ((*FromPiece==WP && GetRank[Move.To]==8) || (*FromPiece==BP && GetRank[Move.To]==1)) {\
		/* Put last location in this position and reduce count */ \
		NewPosition[PieceIndex]=Position[TypeIndex+Position[TypeIndex]]; \
		NewPosition[TypeIndex]--; \
		if (*FromPiece==WP) {\
			switch (Move.PromotionPiece) { \
				case QUEEN 	: NewPosition[WHITEQUEENS]++; NewPosition[WHITEQUEENS+NewPosition[WHITEQUEENS]]=Move.To; break; \
				case KNIGHT : NewPosition[WHITEKNIGHTS]++; NewPosition[WHITEKNIGHTS+NewPosition[WHITEKNIGHTS]]=Move.To; break; \
				case BISHOP : NewPosition[WHITEBISHOPS]++; NewPosition[WHITEBISHOPS+NewPosition[WHITEBISHOPS]]=Move.To; break; \
				case ROOK 	: NewPosition[WHITEROOKS]++; NewPosition[WHITEROOKS+NewPosition[WHITEROOKS]]=Move.To; break; \
				case KING 	: NewPosition[WHITEKINGS]++; NewPosition[WHITEKINGS+NewPosition[WHITEKINGS]]=Move.To; break; \
			} \
		} else { \
			switch (Move.PromotionPiece) { \
				case QUEEN 	: NewPosition[BLACKQUEENS]++; NewPosition[BLACKQUEENS+NewPosition[BLACKQUEENS]]=Move.To; break; \
				case KNIGHT : NewPosition[BLACKKNIGHTS]++; NewPosition[BLACKKNIGHTS+NewPosition[BLACKKNIGHTS]]=Move.To; break; \
				case BISHOP : NewPosition[BLACKBISHOPS]++; NewPosition[BLACKBISHOPS+NewPosition[BLACKBISHOPS]]=Move.To; break; \
				case ROOK 	: NewPosition[BLACKROOKS]++; NewPosition[BLACKROOKS+NewPosition[BLACKROOKS]]=Move.To; break; \
				case KING 	: NewPosition[BLACKKINGS]++; NewPosition[BLACKKINGS+NewPosition[BLACKKINGS]]=Move.To; break; \
			} \
		}\
	} else {\
/* otherwise, change location to Move.To */\
		NewPosition[PieceIndex]=Move.To;\
	}                                   \
/* determine the square index of the captured piece, 0 if none */\
	int CaptureSquare=0;                                          \
	if (*ToPiece!=EMPTY) CaptureSquare=Move.To;          \
	if (*FromPiece==WP && Move.To-Move.From!=1 && Move.To-Move.From!=2 && CaptureSquare==0) CaptureSquare=Move.To-1;\
	if (*FromPiece==BP && Move.From-Move.To!=1 && Move.From-Move.To!=2 && CaptureSquare==0) CaptureSquare=Move.To+1;\
/* if there was a capture then remove piece location */\
	if (CaptureSquare!=0) {                             \
/* determine piece type array location */              \
		TypeIndex=TypeIndexes[Position[CaptureSquare]];    \
/* find captured piece in locations array */            \
		PieceIndex=TypeIndex+1;                           \
		while (Position[PieceIndex]!=CaptureSquare) {      \
			PieceIndex++;                                   \
		} \
/* remove location */ \
/* replace with whichever piece is at the end of the list */ \
/*	and reduce the list size figure by one */ \
		NewPosition[PieceIndex]=NewPosition[TypeIndex+NewPosition[TypeIndex]];\
  /*		NewPosition[TypeIndex+NewPosition[TypeIndex]]=0;  BOLL */ \
		NewPosition[TypeIndex]--;\
	} \
/* if castling move then change position of rook involved */\
	if (*FromPiece==WK) { \
		if (Move.From==51) { \
			if (Move.To==71) { \
				PieceIndex=WHITEROOKS+1;\
				while (Position[PieceIndex]!=81) {\
					PieceIndex++; \
				} \
				NewPosition[PieceIndex]=61;\
			}\
			if (Move.To==31) {\
				PieceIndex=WHITEROOKS+1;\
				while (Position[PieceIndex]!=11) {\
					PieceIndex++;\
				}\
				NewPosition[PieceIndex]=41;\
			}\
		}    \
	}        \
	if (*FromPiece==BK) {\
		if (Move.From==58) {        \
		  if (Move.To==78) {         \
				PieceIndex=BLACKROOKS+1; \
				while (Position[PieceIndex]!=88) {\
					PieceIndex++;                  \
				}\
				NewPosition[PieceIndex]=68;\
		  }                               \
		  if (Move.To==38) {               \
				PieceIndex=BLACKROOKS+1;      \
				while (Position[PieceIndex]!=18) {\
					PieceIndex++;                  \
				}\
				NewPosition[PieceIndex]=48;\
		  }\
		}  \
	}     \
}        \

#define CreateCheckMove(f, t) \
{ \
	TempMoveToTestCheck.From = (f); \
	TempMoveToTestCheck.To = (t); \
	TempMoveToTestCheck.PromotionPiece = EMPTY; \
	TempMoveToTestCheck.Capture = InPosition[(t)]; \
	if (IsCheckingMove(InPosition, TempMoveToTestCheck)) \
	{ \
		MoveArray[++Amount] = TempMoveToTestCheck; \
	} \
}

#define CreateCheckMovePromote(f, t, promote) \
{ \
	TempMoveToTestCheck.From = (f); \
	TempMoveToTestCheck.To = (t); \
	TempMoveToTestCheck.PromotionPiece = promote; \
	TempMoveToTestCheck.Capture = InPosition[(t)]; \
	if (IsCheckingMove(InPosition, TempMoveToTestCheck)) \
	{ \
		MoveArray[++Amount] = TempMoveToTestCheck; \
	} \
}

//  if ((f)==GlobalHashMove.From && (t)==GlobalHashMove.To) \
//  { \
//	Score+=HASHMOVEBONUS; \
//  } \

#define CreateMove(f, t) \
{ \
  Score = (Position[(t)]) == EMPTY ? 0 : (PieceValues[(Position[(t)])]) - (PieceValuesDiv10[(Position[(t)])]);     \
  if (Score<=0) \
  { \
	  u=Amount+1; \
  } \
  else \
  { \
	  u=1; \
	  while (u<=Amount && (int)Score<=MoveArray[u].Score) u++;\
	  for (v=Amount; v>=u; v--) \
	  { \
		  MoveArray[v+1]=MoveArray[v];  \
	  } \
  }; \
  Amount ++; \
  MoveArray[u].From=(f); \
  MoveArray[u].To=(t); \
  MoveArray[u].PromotionPiece=EMPTY;\
  MoveArray[u].Capture=InPosition[(t)]; \
  MoveArray[u].Score = Score;     \
}

#define CreateMove4(f, t, promote) \
{ \
  Score = QUEENVALUE; \
  u=1; \
  while (u<=Amount && (int)Score<=MoveArray[u].Score) u++; \
  for (v=Amount; v>=u; v--) \
  {  \
	  MoveArray[v+1]=MoveArray[v];  \
  } \
  Amount ++; \
  MoveArray[u].From=(f); \
  MoveArray[u].To=(t); \
  MoveArray[u].PromotionPiece=promote;\
  MoveArray[u].Capture=InPosition[(t)]; \
  MoveArray[u].Score = Score;     \
}

#define CreateMove2(f, t) \
{ \
	if (RandomMoveOrder) \
	{ \
		Score=rand() % 1000;  \
	} \
	else \
	{ \
		Score = 0; \
		if (UsePieceSquareValuesInOrdering) \
		switch(Position[(f)]) \
		{ \
			case WP : Score += WhitePawnPieceSquareTable[(t)] - WhitePawnPieceSquareTable[(f)]; break; \
			case WQ : Score += WhiteQueenPieceSquareTable[(t)] - WhiteQueenPieceSquareTable[(f)]; break; \
			case WN : Score += WhiteKnightPieceSquareTable[(t)] - WhiteKnightPieceSquareTable[(f)]; break; \
			case WR : Score += WhiteRookPieceSquareTable[(t)] - WhiteRookPieceSquareTable[(f)]; break; \
			case WB : Score += WhiteBishopPieceSquareTable[(t)] - WhiteBishopPieceSquareTable[(f)]; break; \
			case WK : Score += WhiteKingPieceSquareTable[(t)] - WhiteKingPieceSquareTable[(f)]; break; \
			case BP : Score += BlackPawnPieceSquareTable[(t)] - BlackPawnPieceSquareTable[(f)]; break; \
			case BQ : Score += BlackQueenPieceSquareTable[(t)] - BlackQueenPieceSquareTable[(f)]; break; \
			case BN : Score += BlackKnightPieceSquareTable[(t)] - BlackKnightPieceSquareTable[(f)]; break; \
			case BR : Score += BlackRookPieceSquareTable[(t)] - BlackRookPieceSquareTable[(f)]; break; \
			case BB : Score += BlackBishopPieceSquareTable[(t)] - BlackBishopPieceSquareTable[(f)]; break; \
			case BK : Score += BlackKingPieceSquareTable[(t)] - BlackKingPieceSquareTable[(f)]; break; \
		} \
		Score+=(UseHistory ? History[(f)][(t)] : 0); \
		if (Position[(t)]!=EMPTY) \
		{ \
			Score+=BASECAPTURE; \
			if ((t)==LastMovePiece) Score+=LASTMOVEPIECEBONUS; \
			Score+=(PieceValues[(Position[(t)])]); \
			Score-=(PieceValuesDiv10[(Position[(f)])]); \
		} \
		if ((f)==GlobalHashMove.From && (t)==GlobalHashMove.To) \
		{ \
			Score+=HASHMOVEBONUS; \
		} \
	} \
	if (Score<=0) u=Amount+1; \
	else { \
	  u=1; \
	  while (u<=Amount && (int)Score<=MoveArray[u].Score) u++;\
	  for (v=Amount; v>=u; v--) \
		  MoveArray[v+1]=MoveArray[v];  \
	} ; \
	Amount++; \
	MoveArray[u].From=(f); \
	MoveArray[u].To=(t); \
	MoveArray[u].Score=Score; \
	MoveArray[u].Capture=InPosition[(t)]; \
	MoveArray[u].PromotionPiece=EMPTY; \
}

#define CreateMove3(f, t, promote) \
{ \
	if (RandomMoveOrder) {  \
		Score=rand() % 1000; \
	} else { \
	  Score=(UseHistory ? History[(f)][(t)] : 0); \
	  Score+=PieceValues[promote]; \
	  if (Position[(t)]!=EMPTY) { \
		  Score+=BASECAPTURE; \
		  if ((t)==LastMovePiece) Score+=LASTMOVEPIECEBONUS; \
		  Score+=(PieceValues[(Position[(t)])]);     \
		  Score-=(PieceValuesDiv10[(Position[(f)])]); \
	  } \
	  if ((f)==GlobalHashMove.From && (t)==GlobalHashMove.To) \
			Score+=HASHMOVEBONUS; \
	} \
	if (Score==0) u=Amount+1; \
	else { \
	  u=1; \
	  while (u<=Amount && (int)Score<=MoveArray[u].Score) u++;\
	  for (v=Amount; v>=u; v--) \
		  MoveArray[v+1]=MoveArray[v];  \
	} ; \
	Amount++; \
	MoveArray[u].From=(f); \
	MoveArray[u].To=(t); \
	MoveArray[u].Capture=InPosition[(t)]; \
	MoveArray[u].Score=Score; \
    MoveArray[u].PromotionPiece=promote; \
}

#define CUPDATEHISTORY(from, to) \
	if (UseHistory) { \
		if (Depth<=MAXHISTORYDEPTH && from!=0) { \
			History[(from)][(to)]+=TwoPowers[MAXHISTORYDEPTH-Depth];\
			/*History[(from)][(to)]+=(1 << (MAXHISTORYDEPTH-Depth));*/\
			if (History[(from)][(to)]>HISTORYSCOREMAX) { \
				for (int i=0; i<89; i++) \
					for (int j=0; j<89; j++) \
						History[i][j]/=2; \
			} \
		} \
	}

#define QUPDATEHISTORY(from, to) \
	if (UseHistory) { \
		if (Depth<=MAXHISTORYDEPTH && from!=0) { \
			int InverseDepth = FinalDepth - ((int)Depth < FinalDepth ? Depth : FinalDepth); \
			if (InverseDepth > 0 && Depth < MAXHISTORYDEPTH) \
			{ \
				History[(from)][(to)]=TwoPowers[InverseDepth]; \
				if (History[(from)][(to)]>HISTORYSCOREMAX) { \
					for (int i=0; i<89; i++) \
						for (int j=0; j<89; j++) \
							History[i][j]/=2; \
				} \
			} \
		} \
	}

#define UPDATEHISTORY(from, to) \
	if (UseHistory) { \
		if (Depth<=MAXHISTORYDEPTH && from!=0) \
		{ \
				History[(from)][(to)]++; \
				if (History[(from)][(to)]>HISTORYSCOREMAX) \
				{ \
					for (int i=0; i<89; i++) \
						for (int j=0; j<89; j++) \
						{ \
							History[i][j]/=2; \
						} \
				} \
		} \
	}


#define ReverseNewPathValue \
NewPath.Value=-NewPath.Value; \
if (NewPath.Value>9000) NewPath.Value--; \
if (NewPath.Value<-9000) NewPath.Value++;

#ifdef TESTING
#define TimerAndPVCode \
	timeticker=GetTickCount(); \
	int elapsed = timeticker - searchStartTime; \
	if (searchTimeMillis > 0 && elapsed >= searchTimeMillis) \
	{ \
		if (Satisfied || elapsed > MaxExtendedSearchTimeMillis) \
		{ \
			ExitWithMove(); \
		} \
	} \
	if (lastDisplayedElapsed++ > 500000) \
	{ \
		WritePrincipalPathToGUI(); \
		lastDisplayedElapsed = 0; \
	} 

#else
#define TimerAndPVCode \
	if (++PollCount > POLL_TICKS) \
	{ \
		PollCount = 0; \
		DWORD dw; \
		static HANDLE inh = GetStdHandle(STD_INPUT_HANDLE);\
		GetConsoleMode(inh, &dw);\
		PeekNamedPipe(inh, NULL, 0, NULL, &dw, NULL);\
		if (dw!=NULL && dw>0) ExitWithMove(); \
	} \
	timeticker=GetTickCount(); \
	int elapsed = timeticker - searchStartTime; \
	if (searchTimeMillis > 0 && elapsed >= searchTimeMillis) \
	{ \
		if (Satisfied || elapsed > MaxExtendedSearchTimeMillis) \
		{ \
			ExitWithMove(); \
		} \
	} \
	if (lastDisplayedElapsed++ > 500000) \
	{ \
		WritePrincipalPathToGUI(); \
		lastDisplayedElapsed = 0; \
	} 

#endif