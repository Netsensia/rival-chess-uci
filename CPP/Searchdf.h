#include "newadd.h"

#define LOCKCHECKINHASH

#ifndef SEARCHDF_H
#define SEARCHDF_H
// Define constants that represent indices into the TPosition array.
// We use the position of the white king and black king very often in
// the search and so it is very advantageous to be able to access their
// positions quickly.  TPosition[19]=White King Square.
#define WKINGPOSITION 19
#define BKINGPOSITION 20
#define LASTMOVESQUARE 29
#define WHITECASTLED 39
#define BLACKCASTLED 40
#define HASHKEYFIELD1 49
#ifdef CHARPOSITION
	#define HASHKEYFIELD2 50
	#define HASHKEYFIELD3 59
	#define HASHKEYFIELD4 60
#endif

#define MOVEDIR_UP 1
#define MOVEDIR_DOWN -1
#define MOVEDIR_LEFT -10
#define MOVEDIR_RIGHT 10
#define MOVEDIR_UPLEFT -9
#define MOVEDIR_UPRIGHT 11
#define MOVEDIR_DOWNLEFT -11
#define MOVEDIR_DOWNRIGHT 9

#define WHITEPAWNS 90
#define WHITEKNIGHTS 99
#define WHITEBISHOPS 110
#define WHITEROOKS 121
#define WHITEQUEENS 132
#define WHITEKINGS 142
#define BLACKPAWNS 152
#define BLACKKNIGHTS 161
#define BLACKBISHOPS 172
#define BLACKROOKS 183
#define BLACKQUEENS 194
#define BLACKKINGS 204

#define NUMBEROFPOSITIONELEMENTS (BLACKKINGS+10)

#ifdef CHARPOSITION
	#define POSITIONELEMENT unsigned char
	#define SIZEOFPOSITIONELEMENT 1
#else
	#define POSITIONELEMENT unsigned int
	#define SIZEOFPOSITIONELEMENT 4
#endif

#define SIZEOFPOSITION NUMBEROFPOSITIONELEMENTS*SIZEOFPOSITIONELEMENT

typedef POSITIONELEMENT TPosition[NUMBEROFPOSITIONELEMENTS];

#define HASHDIV3 (128*128*128)
#define HASHDIV2 (128*128)
#define HASHDIV1 128

#ifdef LOCKCHECKINHASH
struct LockStruct
{
	int Lock;
};
#endif

#define SIZEOFLOCKSTRUCT 4
//#define NOPROMOTIONPIECEINHASHMOVE

struct THashMove
{
	char From;
	char To;
#ifndef NOPROMOTIONPIECEINHASHMOVE
	char PromotionPiece;
#endif
#ifdef LOCKCHECKINHASH
	LockStruct Lock;
#endif
	int Value;
	char Depth;
	char Flag;
	char Stale;
};

#ifdef LOCKCHECKINHASH
#ifdef NOPROMOTIONPIECEINHASHMOVE
	#define HASHMOVESIZE 16
#else
	#define HASHMOVESIZE 17
#endif
#else
#ifdef NOPROMOTIONPIECEINHASHMOVE
	#define HASHMOVESIZE (16 - SIZEOFLOCKSTRUCT)
#else
	#define HASHMOVESIZE (17 - SIZEOFLOCKSTRUCT)
#endif
#endif

#endif
