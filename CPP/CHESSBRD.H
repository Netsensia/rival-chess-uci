#ifndef _CHESSBRD_H
#define _CHESSBRD_H

#include <stdio.h>
#include <stdlib.h>
//#include "defines.h"

#define GetX(x) ((x)/10)
#define GetY(x) ((x)%10)

#define TRUE 1
#define FALSE 0

#define MAXOPENINGSREACHED 1

#define VECTORITEMS 500

#define WHITEWIN 0
#define BLACKWIN 1
#define DRAW 2
#define UNKNOWNRESULT 3

#define MOVER 0
#define WROOK1MOVED 1
#define WKINGMOVED 2
#define WROOK8MOVED 3
#define BROOK1MOVED 4
#define BKINGMOVED 5
#define BROOK8MOVED 6
#define ENPAWN 7
#define FIFTYMOVES 8

#define KING 6
#define KNIGHT 2
#define ROOK 4
#define QUEEN 5
#define PAWN 1
#define BISHOP 3

// although these are really arbitary values, I use them to order the
// capture list in the generate module.  No harm will come from altering
// their values so long as they are unique but the program benefits from
// their being ordered.
#define WK 6
#define BK 106
#define WN 2
#define BN 102
#define WR 4
#define BR 104
#define WQ 5
#define BQ 105
#define WP 1
#define BP 101
#define WB 3
#define BB 103
#define EMPTY 50

#define WHITE 0
#define BLACK 1
#define NOCOLOUR 2

#define BACKUP 0
#define RESTORE 1

struct TMove
{
	 char From;
	 char To;
	 char PromotionPiece;
	 char Capture;
	 int Score;
};

#define SIZEOFMOVE 8

#ifndef USE_CLASSLIB

class TArrayAsVectorTMove {
	public:
		TArrayAsVectorTMove() { count=0; };
		void Flush() { count=0; }
		void AddAt(TMove item, int p) { array[p]=item; }
		int Add(TMove item) {
			if (count<VECTORITEMS) {
				array[count++]=item;
				return count;
			} else {
				return 0;
			}
		}
		void SetData(int p, TMove item) {
			if ( p>VECTORITEMS-1 ) p=VECTORITEMS-1;
			array[p]=item;
		}
		int GetItemsInContainer() { return count; }
		TMove& operator[] (unsigned p) {
			if (p>VECTORITEMS-1) p=VECTORITEMS-1;
			return array[p];
		}
	private:
		int count;
		TMove array[VECTORITEMS];
};

class TArrayAsVectorLong {
	public:
		TArrayAsVectorLong() { count=0; };
		void Flush() { count=0; }
		void AddAt(long item, int p) { array[p]=item; }
		int Add(long item) {
			if (count<VECTORITEMS) {
				array[count++]=item;
				return count;
			} else {
				return 0;
			}
		}
		void SetData(int p, long item) {
			if ( p>VECTORITEMS-1 ) p=VECTORITEMS-1;
			array[p]=item;
		}
		int GetItemsInContainer() { return count; }
		long& operator[] (unsigned p) {
			if (p>VECTORITEMS-1) p=VECTORITEMS-1;
			return array[p];
		}
	private:
		int count;
		long array[VECTORITEMS];
};
#endif

class TMoveList
{
  public:
	int Amount;
#ifdef USE_CLASSLIB
	TArrayAsVector<TMove> Moves;
	TMoveList() : Moves(30, 1, 10) {}
#else
	TArrayAsVectorTMove Moves;
	TMoveList() { }
#endif
};

/******************************************/
/* START OF TCHESSBOARD CLASS DEFINITIONS */
/******************************************/
class TChessBoard
{
	public:
	  TChessBoard();
	  TChessBoard(int*);
	  TChessBoard(char*);
	  ~TChessBoard() { };
	  virtual void MakeMove(TMove Move, int Store=TRUE);
	  virtual int VerifyMove(TMove Move);
	  virtual int IsCheck();
	  int GetSquare(int i);
	  int GetMover();
	  virtual int GameStatus();
	  void SetResigned(int);
	  void SetDrawAgreed(int);
	  void SetWhiteClock(long);
	  void SetBlackClock(long);
	  void SetWhiteStart(long);
	  void SetBlackStart(long);
	  long GetWhiteClock();
	  long GetBlackClock();
	  void SaveGame(char* FileName);
	  void SavePGN(char* FileName, int, char*);
	  void LoadGame(char* FileName);
	  void TakeBackMove();
	  void TakeBackAllMoves();
	  int TotalMovesMade(); // Total Number of Moves available, regardless of current board-state
	  int LastMoveMade(); // Move Number that caused current board-state
	  void ReplayMove();
	  void ReplayAllMoves();
	  TMove GetMove(int number);
	  virtual int GetMoveList(TMoveList& List);
	  TMoveList GetPreviousMoves();
	  char ToPieceChar(int SquareID);
	  void BackUpBoard(int direction); // some functions may need to change the board temporarily
	  int Square[89];
	  TMove GetLastMoveDetails();
	  void TranslateMoveToAlgebraic(char *s, TMove);
	  int TranslateFenToBoard(char* s, int* SetupBoard);
	  int ReadPGN(FILE *input, int option);
	  int TranslateAlgebraicMove(char *text, TMove&);
	  void LoadPGN(char* FileName);
	  int IsOriginalPosition();
	  int IsGameSaved();
#ifdef USE_CLASSLIB
	  TArrayAsVector<TMove> MovesMade;
	  TArrayAsVector<long> WhiteClocks;
	  TArrayAsVector<long> BlackClocks;
#else
	  TArrayAsVectorTMove MovesMade;
	  TArrayAsVectorLong WhiteClocks;
	  TArrayAsVectorLong BlackClocks;
#endif
	  int ThirdRepetition();
	  void GetFEN(char*, int, int);
	  int ResetTo[89];
	  char buffer[512];
	  int GameSaved;
	  void ResetBoard();
	  int MovePointer;
	  int MovesStored;
	protected:
	  int BackUpSquare[89]; // used by BackUp- and RestoreBoard
	  int Resigned;
	  int DrawAgreed;
	private:
	  void Initialise();
	  long WhiteClock, BlackClock;
	  int OriginalPosition;
	  int ToPieceValue(char SquareID);
	  long MakeStorable(TMove Move);
	  void AddMove(TMoveList& List, int Fx, int Fy, int Tx, int Ty);
};
#endif
