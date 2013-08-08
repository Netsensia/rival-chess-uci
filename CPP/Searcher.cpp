#pragma unmanaged

#include <ctime>
#include <xutility>
#include <stdlib.h>
#include <math.h>
#include <windows.h>
#include <string.h>
#include <string>
#include <fstream>
#include <iostream>
#pragma hdrstop
#include "newrival.h"
#include "searcher.h"
#include "chessbrd.h"
#include "logger.h"

using namespace std;

int PollCount = 0;

#ifdef TESTING
	int RecaptureExtensionsCount = 0;
	int FailHighReductionsCount = 0;
	int PawnPushExtensionsCount = 0;
	int CheckExtensionsCount = 0;
	int NullMoveAttemptsCount = 0;
	int NullMoveCutoffsCount = 0;
	int NullMoveReductionsCount = 0;
	int ZugzwangCount = 0;
	int FutilityPrunes1Count = 0;
	int FutilityPrunes2Count = 0;
	int UnverifiedHashEntries = 0;
	int HashAttemptsInQuiesce = 0;
	int SuccessfullHashAttemptsInQuiesce = 0;
	int UselessHashRetrievalsInQuiesce = 0;
	int AlwaysReplaceRetrieveCount = 0;
	int AlwaysReplaceRetrieveAttemptCount = 0;
	int DepthHashRetrieveCount = 0;
	int DepthHashRetrieveAttemptCount = 0;
	int TotalQuiesceCheckCount = 0;
	int HashSuccessCount = 0;
	int DepthHashSuccessCount = 0;
	int AlwaysReplaceHashSuccessCount = 0;
	
	bool IsAlwaysReplaceRetrieval;

	int TotalGetMoveListCalls = 1;
	int TotalGetMoveListMillis = 0;
	int TotalIsCheckCalls = 1;
	int TotalIsCheckMillis = 0;
	int TotalGetQuickMoveListCalls = 1;
	int TotalGetQuickMoveListMillis = 0;
	int TotalGetCheckMoveListCalls = 1;
	int TotalGetCheckMoveListMillis = 0;
	int TotalEvaluateCalls = 1;
	int TotalEvaluateMillis = 0;
	int TotalIsCheckingMoveCalls = 1;
	int TotalIsCheckingMoveMillis = 0;

	int ShownPositions = 0;

	int TotalIsAttackedCalls = 1;
	int TotalIsAttackedMillis = 0;
	int TotalFirstPieceCalls = 1;
	int TotalFirstPieceMillis = 0;
	int TotalIsDiscoveredCheckCalls = 1;
	int TotalIsDiscoveredCheckMillis = 0;

#endif

// for intercepting UCI commands
char* CommandString = new char[STRING_SIZE];

int lastDisplayedElapsed = -1;

char logtextsearcher[LOGTEXTSIZE];

#define POSITIONALMAX 1800

// When we grab the time it won't be necessarily 1 ms after the last time, so we give a window within which it will trigger an info message
#define SHOW_INFO_MILLIS 750
#define SHOW_INFO_WINDOW 100

#undef TESTWHITEPASSEDPAWNS
#undef TESTBLACKPASSEDPAWNS
#undef NOZORBRIST
#undef FILTERHASH
#undef TESTVERIFY
#undef HASHCHECK
#undef POSITIONALEVAL
#undef TESTLOCATIONS
#undef WRITEMOVES
#undef FIRSTEVALONLY

#ifdef POSITIONALEVAL
	 int MaxPositional=-100000;
	 int MinPositional=100000;
	 int Segments[70];
	 int TPCount=1;
	 int TPTotal=0;
#endif

int BlackPawnAdvance[88];

unsigned int i, y, a;
unsigned int Square;
unsigned int wnp, bnp;

// For speed, to avoid declaration each time
int FirstPieceLoop;
bool ViaSquareHit;

POSITIONELEMENT *p;
POSITIONELEMENT *Wpf;
POSITIONELEMENT *Bpf;
POSITIONELEMENT *Wpfi, *Bpfi;
int WhiteScore, BlackScore;

int TwoPowers[20]= {
	1,
	2,
	4,
	8,
	16,
	32,
	64,
	128,
	256,
	512,
	1024,
	2048,
	4096,
	8192,
	16384,
	32768,
	65536,
	131072,
	262144,
	524288
};

TSearcher::TSearcher(int CommandLineHashSize)
{
	PieceValues[PAWN+100]=PieceValues[PAWN]=PAWNVALUE/10;
	PieceValues[KNIGHT+100]=PieceValues[KNIGHT]=KNIGHTVALUE/10;
	PieceValues[BISHOP+100]=PieceValues[BISHOP]=BISHOPVALUE/10;
	PieceValues[ROOK+100]=PieceValues[ROOK]=ROOKVALUE/10;
	PieceValues[QUEEN+100]=PieceValues[QUEEN]=QUEENVALUE/10;
	PieceValuesDiv10[PAWN+100]=PieceValuesDiv10[PAWN]=PieceValues[PAWN]/30;
	PieceValuesDiv10[KNIGHT+100]=PieceValuesDiv10[KNIGHT]=PieceValues[KNIGHT]/30;
	PieceValuesDiv10[BISHOP+100]=PieceValuesDiv10[BISHOP]=PieceValues[BISHOP]/30;
	PieceValuesDiv10[ROOK+100]=PieceValuesDiv10[ROOK]=PieceValues[ROOK]/30;
	PieceValuesDiv10[QUEEN+100]=PieceValuesDiv10[QUEEN]=PieceValues[QUEEN]/30;

	int i;

	for (i=0; i<MAXHISTORYDEPTH; i++)
	{
		TwoPowers[i] = (int)(TwoPowers[i]);
	}

	SetupTropism();

	DebugCounter = 0;

	StopMove.From=0;
    StopScore=-32100;
	MaxDepth=100;
	MaxQuiesceDepth=50;
	LowEval=LOWEVAL;
	HighEval=HIGHEVAL;

	UseCheckExtensions=TRUE;
	UsePawnPushExtensions=TRUE;
	UseSingleReplyExtensions=TRUE;

	MaxExtendedSearchTimeMillis = 0;

	UseOpeningLibrary = false;
	PrintPV=FALSE;
	NullMoveReduceDepth=1;
    PrincipalPath.Move[0].From=0;
	MinimumMate=9000;
	LastMoveNumber=0;

#ifdef TESTING
	cout << "Hash Move Size = " << HASHMOVESIZE << LOG_ENDL;
#endif
	
#ifdef USE_TWO_HASH_TABLES
	long ByteSize=(CommandLineHashSize*1024) / 2;
	long ByteSizeAlwaysReplace = ByteSize;
#else
	long ByteSize=(CommandLineHashSize*1024);
#endif

	long j=1;
	for (long i=1; i<31; i++) 
	{
		j*=2;
#ifdef USE_TWO_HASH_TABLES
		if (j*HASHMOVESIZE>=max(ByteSize,ByteSizeAlwaysReplace))
#else
		if (j*HASHMOVESIZE>=ByteSize)
#endif
		{
			HashPower=i;
			break;
		}
	}
	NumberOfHashEntries=ByteSize/HASHMOVESIZE;
#ifdef USE_TWO_HASH_TABLES
	NumberOfHashEntriesAlwaysReplace=ByteSizeAlwaysReplace/HASHMOVESIZE;
#endif
	if (NumberOfHashEntries<1) 
	{
		NumberOfHashEntries=1;
#ifdef USE_TWO_HASH_TABLES
		NumberOfHashEntriesAlwaysReplace=1;
#endif
		HashPower=1;
	}

#ifdef TESTING
#ifdef USE_TWO_HASH_TABLES
	printf("Hash entries (depth preferred) %i\r\n", NumberOfHashEntries);
	printf("Hash entries (always replace) %i\r\n", NumberOfHashEntriesAlwaysReplace);
#else
	printf("Hash entries %i\r\n", NumberOfHashEntries);
#endif
	printf("Hash power %i\r\n", HashPower);
#endif
	HashTable = new THashMove[NumberOfHashEntries];
#ifdef USE_TWO_HASH_TABLES
	HashTableAlwaysReplace = new THashMove[NumberOfHashEntriesAlwaysReplace];
#endif

	GeneratePieceValues();
}

TSearcher::~TSearcher()
{
	delete[] HashTable;
#ifdef USE_TWO_HASH_TABLES
	delete[] HashTableAlwaysReplace;
#endif
}

void
TSearcher::GeneratePieceValues()
{
#ifdef HASHTABLE
	int HashPieceSquareValueMax=CalculateHashSize(HashPower);
	int i, j;
	for (i=0; i<89; i++)
		for (j=0; j<12; j++) {
			int temp = (rand() * rand()) % HashPieceSquareValueMax;
			PieceSquareValues[i][j]=temp;
		}
	ClearHashTable();
#ifdef LOCKCHECKINHASH
	// These values are used to generate the lock key for a hash table entry
	for (i=0; i<89; i++)
		for (j=0; j<12; j++) {
			LockPieceSquareValues[i][j]=(rand() * rand()) % 2147483647L;
		}
#endif

#endif
}

void
TSearcher::SetMaxDepth(int NewMaxDepth)
{
	MaxDepth=NewMaxDepth;
}

int
TSearcher::CalculateHashSize(int hashpower) 
{
	int rv = 1;
	for (int i=0; i<hashpower; i++) {
		rv*=2;
	}
	return rv;
}

void 
TSearcher::StoreHashMoveDetails(TPosition Position, int Height, int Flag, TMove Move, int Value)
{
#ifdef NOZORBRIST
	 int HashKey=ComputeHashKey(Position);
#else
	 int HashKey=Position[HASHKEYFIELD1];
#endif

	 if ((unsigned int)HashKey>=NumberOfHashEntries) 
	 {
		 HashKey=HashKey % NumberOfHashEntries;
	 }
	 THashMove* HashLocation=HashTable+HashKey;
#ifdef USE_TWO_HASH_TABLES
	 if (HashLocation->Depth>Height && !HashLocation->Stale)
	 {
		// Existing entry is better depth and is not stale, put in replacable table
		if ((unsigned int)HashKey>=NumberOfHashEntriesAlwaysReplace) 
		{
			HashKey=HashKey % NumberOfHashEntriesAlwaysReplace;
		}
		HashLocation = HashTableAlwaysReplace + HashKey;
	 }
#else
	 if (HashLocation->Depth<=Height || HashLocation->Stale)
#endif
	 {
		HashLocation->From=Move.From;
		HashLocation->To=Move.To;
#ifndef NOPROMOTIONPIECEINHASHMOVE
		HashLocation->PromotionPiece=Move.PromotionPiece;
#endif

#ifdef LOCKCHECKINHASH
		HashLocation->Lock=EncodePosition(Position);
#endif
		HashLocation->Depth=Height;
		HashLocation->Value=Value;
		HashLocation->Flag=Flag;
		HashLocation->Stale=FALSE;
	 }
}

void
TSearcher::GetHashMoveDetails(TPosition Position, int& Height, int& Flag, TMove& Move, int& Value)
{
	//return;
#ifdef TESTING
	DepthHashRetrieveAttemptCount ++;
	IsAlwaysReplaceRetrieval = false;
#endif
//	TimerAndPVCode;
#ifdef NOZORBRIST
	long HashKey=ComputeHashKey(Position);
#else
	long HashKey=Position[HASHKEYFIELD1];
#endif
	if ((unsigned int)HashKey>=NumberOfHashEntries) 
	{
		HashKey=HashKey % NumberOfHashEntries;
	}
#ifdef LOCKCHECKINHASH
	LockStruct TempLock = EncodePosition(Position);
	if (HashTable[HashKey].Lock.Lock==TempLock.Lock) 
#endif
	{
#ifdef TESTING
	  DepthHashRetrieveCount ++;
#endif
	  Height=HashTable[HashKey].Depth;
	  Flag=HashTable[HashKey].Flag;
	  Value=HashTable[HashKey].Value;
	  Move.From=HashTable[HashKey].From;
	  Move.To=HashTable[HashKey].To;
#ifndef NOPROMOTIONPIECEINHASHMOVE
	  Move.PromotionPiece = HashTable[HashKey].PromotionPiece;
#endif
	  HashTable[HashKey].Stale=FALSE;
	} 
#ifdef LOCKCHECKINHASH	
	else 
	{
	  Height=0;
	}
#endif

#ifdef USE_TWO_HASH_TABLES
	if (Height == 0)
	{
		if ((unsigned int)HashKey>=NumberOfHashEntriesAlwaysReplace) 
		{
			HashKey=HashKey % NumberOfHashEntriesAlwaysReplace;
		}
#ifdef TESTING
		AlwaysReplaceRetrieveAttemptCount ++;
		IsAlwaysReplaceRetrieval = true;
#endif
#ifdef LOCKCHECKINHASH
		if (HashTableAlwaysReplace[HashKey].Lock.Lock==TempLock.Lock)
#endif
		{
#ifdef TESTING
				AlwaysReplaceRetrieveCount ++;
#endif
				Height=HashTableAlwaysReplace[HashKey].Depth;
				Flag=HashTableAlwaysReplace[HashKey].Flag;
				Value=HashTableAlwaysReplace[HashKey].Value;
				Move.From=HashTableAlwaysReplace[HashKey].From;
				Move.To=HashTableAlwaysReplace[HashKey].To;
#ifndef NOPROMOTIONPIECEINHASHMOVE
				Move.PromotionPiece = HashTableAlwaysReplace[HashKey].PromotionPiece;
#endif
				HashTableAlwaysReplace[HashKey].Stale=FALSE;
			}
	}
#endif
}

int
TSearcher::ComputeHashKey(TPosition Position)
{
	long HashKey=0;
	int x, y, SqIndex, Piece;
	for (x=9; --x; )
	  for (y=9; --y; ) {
		  if (Position[x*10+y]!=EMPTY) {
			 SqIndex=x*10+y;
			 Piece=Position[SqIndex];
			 if (Piece>100) Piece-=95; else Piece-=1;
			 HashKey^=(PieceSquareValues[SqIndex][Piece]);
		  }
	  }
	if (Position[MOVER]==WHITE)
		HashKey^=(PieceSquareValues[MOVER][WHITE]);
	else
		HashKey^=(PieceSquareValues[MOVER][BLACK]);

#ifdef TESTING
	printf("Computed Hash key %i\r\n", HashKey);
#endif
	return HashKey;
}

#ifdef LOCKCHECKINHASH
LockStruct
TSearcher::EncodePosition(TPosition Position)
{
	LockStruct RetLock;
	unsigned long HashKey=0;
	int x, y, SqIndex, Piece;
	for (x=1; x<=8; x++)
	{
	  for (y=1; y<=8; y++) 
	  {
		  SqIndex=x*10+y;
		  Piece=Position[SqIndex];
		  if (Piece!=EMPTY) 
		  {
			 if (Piece>100) 
			 {
				 Piece-=95; 
			 }
			 else 
			 {
				 Piece-=1;
			 }
			 HashKey^=(LockPieceSquareValues[SqIndex][Piece]);
		  }
	  }
	}
	HashKey^=(LockPieceSquareValues[MOVER][Position[MOVER]]);
	HashKey^=(LockPieceSquareValues[WROOK1MOVED][Position[WROOK1MOVED]]);
	HashKey^=(LockPieceSquareValues[WROOK8MOVED][Position[WROOK8MOVED]]);
	HashKey^=(LockPieceSquareValues[BROOK1MOVED][Position[BROOK1MOVED]]);
	HashKey^=(LockPieceSquareValues[BROOK8MOVED][Position[BROOK8MOVED]]);
	HashKey^=(LockPieceSquareValues[WKINGMOVED][Position[WKINGMOVED]]);
	HashKey^=(LockPieceSquareValues[BKINGMOVED][Position[BKINGMOVED]]);
	HashKey^=(LockPieceSquareValues[ENPAWN][Position[ENPAWN]]);

	RetLock.Lock=HashKey;

	return RetLock;
}
#endif

void
TSearcher::ClearHashTable()
{
	int i;
	for (i=NumberOfHashEntries; i--;) {
		HashTable[i].Depth=0;
		HashTable[i].From=0;
		HashTable[i].To=0;
		HashTable[i].Value=0;
		HashTable[i].Flag=0;
		HashTable[i].Stale=FALSE;
#ifdef LOCKCHECKINHASH
		HashTable[i].Lock.Lock=0;
#endif
	}
}

void
TSearcher::StaleHashTable()
{
	int i;
	for (i=NumberOfHashEntries; i--; ) {
		HashTable[i].Stale=TRUE;
	}
}

void
TSearcher::ClearHistory()
{
	for (int i=89; i--; ) {
		for (int j=89; j--; ) {
			History[i][j]=0;
		}
	}
}

void
TSearcher::SetMaxQuiesceDepth(int NewQuiesceDepth)
{
	MaxQuiesceDepth=NewQuiesceDepth;
}

int
TSearcher::GetCurrentPathNodes()
{
	return CurrentPathNodes;
}

TPath
TSearcher::GetPrincipalPath()
{
	PrincipalPath.Nodes=CurrentPathNodes;
	return PrincipalPath;
}

void
TSearcher::ExitWithoutMove()
{
	ExitCode=1;
}

void
TSearcher::ExitWithMove()
{
/*************************************************************************
Only exit with move if a move has been found.
**************************************************************************/
	if (FinalDepth>2 && PrincipalPath.Move[0].From!=0) ExitCode=2;
}

TPath
TSearcher::Search()
{
	searchStartTime = GetTickCount();

	TPath NewPath;
	int i;
	ExitCode=0;
	ClearHistory();
	PrincipalPath.Move[0].From=0; // In case of interuption when move is required, signals no move available
	CurrentPathNodes=1;
	GlobalHashMove.From=0;

	int WhiteRootMaterial =
		  StartPosition[WHITEQUEENS]*QUEENVALUE+
		  StartPosition[WHITEBISHOPS]*BISHOPVALUE+
		  StartPosition[WHITEKNIGHTS]*KNIGHTVALUE+
		  StartPosition[WHITEROOKS]*ROOKVALUE+
		  StartPosition[WHITEPAWNS]*PAWNVALUE;

	int BlackRootMaterial =
		  StartPosition[BLACKQUEENS]*QUEENVALUE+
		  StartPosition[BLACKBISHOPS]*BISHOPVALUE+
		  StartPosition[BLACKKNIGHTS]*KNIGHTVALUE+
		  StartPosition[BLACKROOKS]*ROOKVALUE+
		  StartPosition[BLACKPAWNS]*PAWNVALUE;

	RootMaterial=WhiteRootMaterial - BlackRootMaterial;

	if (WhiteRootMaterial < DEFAULT_STOP_PST_AT_MATERIAL || BlackRootMaterial < DEFAULT_STOP_PST_AT_MATERIAL)
	{
		UsePieceSquareValuesInOrdering = false;
	}
	else
	{
		UsePieceSquareValuesInOrdering = DEFAULT_USE_PIECE_SQUARE_VALUES_IN_ORDERING;
	}

	if (WhiteRootMaterial < 10000 || BlackRootMaterial < 10000)
	{
		UseFailHighReductions = 0;
	}

	ValueGuess=Evaluate(StartPosition, LOWEVAL, HIGHEVAL);
#ifdef FIRSTEVALONLY
	ExitWithoutMove();
#endif
	CurrentDepth=0;
	Depth0Amount=GetMoveList(StartPosition, Moves[0]);

	for (i=1; i<=Depth0Amount; i++) {
		Moves[0][i].Score=LowEval;
	}

	PIBest=LowEval;
	Satisfied=TRUE;

	int c=0;
	TPosition NewPosition;
	for (i=1; i<=Depth0Amount; i++) 
	{
	  if (MakeMove(StartPosition, Moves[0][i], NewPosition)) 
	  {
		 c++;
	  }
	}

	CurrentDepthZeroMove.From=0;
	FinalQuiesceDepth=MaxQuiesceDepth;
	int LowAspire, HighAspire;
	FinalDepth=1;

#ifdef VERBOSE_LOGGING
	sprintf_s(logtextsearcher, LOGTEXTSIZE, "About to determine aspiration window");
	WriteLog(logtextsearcher);
#endif

	MinimaxZero(StartPosition, 0, LOWEVAL, HIGHEVAL, &NewPath, 0);

	ReOrderMoves(Moves[0], Depth0Amount);

	LowAspire=-NewPath.Value-(AspireWindow/2);
	HighAspire=-NewPath.Value+(AspireWindow/2);
	CurrentPathNodes=1;
	if (c>1)
	for (FinalDepth=2; FinalDepth<=MaxDepth; FinalDepth++) {

#ifdef VERBOSE_LOGGING
	sprintf_s(logtextsearcher, LOGTEXTSIZE, "Now searching to depth %i", FinalDepth);
	WriteLog(logtextsearcher);
#endif

#ifdef POSITIONALEVAL
FILE* f=fopen( "c:\\log.txt", "a" );
fprintf( f, "-----------------------------------------------------------------------------\n" );
fprintf( f, "TP %i, TPCount %i, TPAverage %i Max Positional: %i, Min Positional: %i\n", TPTotal, TPCount, TPTotal/TPCount, MaxPositional, MinPositional);
fprintf( f, "-----------------------------------------------------------------------------\n" );
for (i=0; i<=60; i++) {
	fprintf( f, "%i\t", (i-30)*100 );
}
fprintf( f, "\n" );
for (i=0; i<=60; i++) {
	fprintf( f, "%i\t", Segments[i] );
}
fprintf( f, "\n-----------------------------------------------------------------------------\n" );
fclose(f);
#endif
		CurrentDepthZeroMove.From=0;
		if (MinimumMate>9000 && (10000-MinimumMate-FinalDepth-2)<MaxExtensions) {
			MaxExtensions=(10000-MinimumMate-FinalDepth-2);
			if (MaxExtensions<0) MaxExtensions=0;
		}
#ifdef VERBOSE_LOGGING
			sprintf_s(logtextsearcher, LOGTEXTSIZE, "Searching with %i to %i", LowAspire, HighAspire);
			WriteLog(logtextsearcher);
#endif
		MinimaxZero(StartPosition, 0, LowAspire, HighAspire, &NewPath, 0);
		if (NewPath.Value<=LowAspire) {
			CurrentDepthZeroMove.From=0;
#ifdef VERBOSE_LOGGING
			sprintf_s(logtextsearcher, LOGTEXTSIZE, "Failed Low Searching Again with %i to %i", LowEval, HighAspire);
			WriteLog(logtextsearcher);
#endif
			MinimaxZero(StartPosition, 0, LowEval, HighAspire, &NewPath, 0);
		} else
		if (NewPath.Value>=HighAspire) 
		{
			CurrentDepthZeroMove.From=0;
#ifdef VERBOSE_LOGGING
			sprintf_s(logtextsearcher, LOGTEXTSIZE, "Failed High Searching Again with %i to %i", LowAspire, HighEval);
			WriteLog(logtextsearcher);
#endif
			MinimaxZero(StartPosition, 0, LowAspire, HighEval, &NewPath, 0);
		}
		WritePrincipalPathToGUI();
		HighAspire = NewPath.Value + (AspireWindow/2);
		LowAspire = NewPath.Value - (AspireWindow/2);
		NewPath.Nodes=CurrentPathNodes;
		if (ExitCode==1) NewPath.Move[0].From=0; // Exit with no move required
		if (ExitCode==2) {
			// interupted but move required
			if (PrincipalPath.Value>MinimumMate) {
				MinimumMate=PrincipalPath.Value;
			}
			return PrincipalPath;
		}
		if (NewPath.Move[0].From==0) return NewPath; // no move available
		memcpy(&PrincipalPath, &NewPath, SIZEOFPATH);
		PrincipalPath.Depth=FinalDepth;
		PIBest=PrincipalPath.Value;
		Satisfied=(PIBest>ValueGuess-SATISFACTION);
		ValueGuess=PIBest;
		ReOrderMoves(Moves[0], Depth0Amount);
#ifdef VERBOSE_LOGGING
		char moveString[7];
		GetSimpleMoveString(NewPath.Move[0], moveString);
		sprintf_s(logtextsearcher, LOGTEXTSIZE, "I like move %s because it scored %i", moveString, NewPath.Value);
		WriteLog(logtextsearcher);
#endif
	}
	if (c==0) PrincipalPath.Nodes=0;
#ifdef TESTING
	cout << "Recapture Extensions " << RecaptureExtensionsCount << LOG_ENDL;
	cout << "Check Extensions " << CheckExtensionsCount << LOG_ENDL;
	cout << "Pawn Push Extensions " << PawnPushExtensionsCount << LOG_ENDL;
	cout << "Fail High Reductions " << FailHighReductionsCount << LOG_ENDL;
	cout << "Null Move Attempts " << NullMoveAttemptsCount << LOG_ENDL;
	cout << "Null Move Reductions " << NullMoveReductionsCount << LOG_ENDL;
	cout << "Null Move Cutoffs " << NullMoveCutoffsCount << LOG_ENDL;
	cout << "Zugzwangs " << ZugzwangCount << LOG_ENDL;
	cout << "Unverified Hash Entries " << UnverifiedHashEntries << LOG_ENDL;
	cout << "Hash Attempts in Quiesce " << HashAttemptsInQuiesce << LOG_ENDL;
	cout << "Successfull Attempts in Quiesce " << SuccessfullHashAttemptsInQuiesce << LOG_ENDL;
	cout << "Useless Hash Retrievals in Quiesce " << UselessHashRetrievalsInQuiesce << LOG_ENDL;
	cout << "Futility Prunes 1 " << FutilityPrunes1Count << LOG_ENDL;
	cout << "Futility Prunes 2 " << FutilityPrunes2Count << LOG_ENDL;

	cout << LOG_ENDL;

	cout << "Depth Retrieval Attempts " << DepthHashRetrieveAttemptCount << LOG_ENDL;
	cout << "Depth Retrieves " << DepthHashRetrieveCount << LOG_ENDL;
	cout << "Always Replace Retrieval Attempts " << AlwaysReplaceRetrieveAttemptCount << LOG_ENDL;
	cout << "Always Replace Retrieves " << AlwaysReplaceRetrieveCount << LOG_ENDL;
	cout << "Good Hash Retrieves " << HashSuccessCount << LOG_ENDL;
	cout << "Good Hash Retrieves (Depth) " << DepthHashSuccessCount << LOG_ENDL;
	cout << "Good Hash Retrieves (Always Replace) " << AlwaysReplaceHashSuccessCount << LOG_ENDL;

	cout << LOG_ENDL;

	cout << "Total Quiesce Check " << TotalQuiesceCheckCount << LOG_ENDL;

	cout << LOG_ENDL;

	char s[100];

	cout << "GetMoveList() Calls " << TotalGetMoveListCalls << LOG_ENDL;
	cout << "GetMoveList() Millis " << TotalGetMoveListMillis << LOG_ENDL;
	sprintf_s(s, "%.6f", ((double)TotalGetMoveListMillis / TotalGetMoveListCalls));
	cout << "GetMoveList() Per Call " << s << LOG_ENDL;

	cout << "GetQuickMoveList() Calls " << TotalGetQuickMoveListCalls << LOG_ENDL;
	cout << "GetQuickMoveList() Millis " << TotalGetQuickMoveListMillis << LOG_ENDL;
	sprintf_s(s, "%.6f", ((double)TotalGetQuickMoveListMillis / TotalGetQuickMoveListCalls));
	cout << "GetQuickMoveList() Per Call " << s << LOG_ENDL;

	cout << "IsCheck() Calls " << TotalIsCheckCalls << LOG_ENDL;
	cout << "IsCheck() Millis " << TotalIsCheckMillis << LOG_ENDL;
	sprintf_s(s, "%.6f", ((double)TotalIsCheckMillis / TotalIsCheckCalls));
	cout << "IsCheck() Per Call " << s << LOG_ENDL;

	cout << "GetCheckMoveList() Calls " << TotalGetCheckMoveListCalls << LOG_ENDL;
	cout << "GetCheckMoveList() Millis " << TotalGetCheckMoveListMillis << LOG_ENDL;
	sprintf_s(s, "%.6f", ((double)TotalGetCheckMoveListMillis / TotalGetCheckMoveListCalls));
	cout << "GetCheckMoveList() Per Call " << s << LOG_ENDL;

	cout << "Evaluate() Calls " << TotalEvaluateCalls << LOG_ENDL;
	cout << "Evaluate() Millis " << TotalEvaluateMillis << LOG_ENDL;
	sprintf_s(s, "%.6f", ((double)TotalEvaluateMillis / TotalEvaluateCalls));
	cout << "Evaluate() Per Call " << s << LOG_ENDL;

	cout << "IsCheckingMove() Calls " << TotalIsCheckingMoveCalls << LOG_ENDL;
	cout << "IsCheckingMove() Millis " << TotalIsCheckingMoveMillis << LOG_ENDL;
	sprintf_s(s, "%.6f", ((double)TotalIsCheckingMoveMillis / TotalIsCheckingMoveCalls));
	cout << "IsCheckingMove() Per Call " << s << LOG_ENDL;

	cout << "IsAttacked() Calls " << TotalIsAttackedCalls << LOG_ENDL;
	cout << "IsAttacked() Millis " << TotalIsAttackedMillis << LOG_ENDL;
	sprintf_s(s, "%.6f", ((double)TotalIsAttackedMillis / TotalIsAttackedCalls));
	cout << "IsAttacked() Per Call " << s << LOG_ENDL;

	cout << "FirstPieceOnLineViaSquare() Calls " << TotalFirstPieceCalls << LOG_ENDL;
	cout << "FirstPieceOnLineViaSquare() Millis " << TotalFirstPieceMillis << LOG_ENDL;
	sprintf_s(s, "%.6f", ((double)TotalFirstPieceMillis / TotalFirstPieceCalls));
	cout << "FirstPieceOnLineViaSquare() Per Call " << s << LOG_ENDL;

	cout << "IsDiscoveredCheck() Calls " << TotalIsDiscoveredCheckCalls << LOG_ENDL;
	cout << "IsDiscoveredCheck() Millis " << TotalIsDiscoveredCheckMillis << LOG_ENDL;
	sprintf_s(s, "%.6f", ((double)TotalIsDiscoveredCheckMillis / TotalIsDiscoveredCheckCalls));
	cout << "IsDiscoveredCheck() Per Call " << s << LOG_ENDL;

#endif
	return PrincipalPath;
}

void
TSearcher::Quiesce(TPosition Position, int Depth, int Lowest, int Highest, TPath* Path, int ExtendDepth, int CheckExtends, int NewPositionCheck)
{
#ifdef USINGALLMOVESINQUIESCE
	  int All=FALSE;
#endif
	  int Legal=TRUE;
	  int NumberOfMoves;
	  TMove* move;
	  TPath NewPath;
	  TPath BestPath;

#ifdef USEHASHINQUIESCE

	TMove* BestPathMove=&BestPath.Move[Depth];
	GlobalHashMove.From=0;
	BestPathMove->From=0;
	int Height = 0;
	int Flag;
	GetHashMoveDetails(Position, Height, Flag, *BestPathMove, BestPath.Value);
#ifdef TESTING
	HashAttemptsInQuiesce ++;
#endif
	if (Height>0 && BestPathMove->From!=0) 
	{
#ifdef TESTING
		if (!VerifyMove(Position, *BestPathMove)) 
		{
			UnverifiedHashEntries++;
			Height=0;
		}
#endif
		if (Height>0) 
		{
			GlobalHashMove=*BestPathMove;
#ifdef TESTING
			SuccessfullHashAttemptsInQuiesce ++;
#endif
			Path->Move[Depth]=*BestPathMove;
			Path->Move[Depth].Capture=Position[BestPathMove->To];
			Path->Move[Depth+1].From=0;

#ifdef TESTING
			bool IsUseless = true;
#endif

			if (Flag == LBOUND && BestPath.Value > Lowest)
			{
				Lowest = BestPath.Value;
#ifdef TESTING
				IsUseless = false;
#endif
			}
			else if (Flag == UBOUND && BestPath.Value < Highest)
			{
				Highest = BestPath.Value;
#ifdef TESTING
				IsUseless = false;
#endif
			}
			
			if (Flag==VALID || Lowest > Highest)
			{
				goto done;
			}

#ifdef TESTING
			if (IsUseless)
			{
				UselessHashRetrievalsInQuiesce ++;
			}
#endif
		}
	}
#endif

#ifdef USINGALLMOVESINQUIESCE
	  int ThisPositionCheck = NewPositionCheck;
	  if (!NewPositionCheck)
	  {
		  ThisPositionCheck = IsCheck(Position);
	  }
	  if (Depth<(FinalDepth+ExtendDepth)+FinalQuiesceDepth) 
	  {
			All=((FinalDepth+ExtendDepth)!=Depth) && ThisPositionCheck;
	  }
	  if (!All) 
	  {
#endif
			Path->Value=Evaluate(Position, Lowest, Highest);
			Path->Move[Depth].From=0;
			if (Path->Value>=Highest) 
			{
				return;
			}
#ifdef USINGALLMOVESINQUIESCE
	  } else {
			Path->Value=-10000;
			Legal=FALSE;
	  }
#ifdef COUNTNODESINQUIESCE
	  CurrentPathNodes ++;
#endif
	  if (All) {
			CurrentDepth=Depth;
			NumberOfMoves=GetMoveList(Position, Moves[Depth]);
	  } 
	  else 
	  {
		NumberOfMoves=GetQuickMoveList(Position, Moves[Depth]);
	  }
#else
	  NumberOfMoves=GetQuickMoveList(Position, Moves[Depth]);
#endif

/*************************************************************************
Effectively make a null-move.  If we imagine that all we do is swap the
side to move, then we would value this move as -Evaluate(Position).
To achieve the same result, we just take the value Evaluate(Position) as
the value of the null-move.  If our capture tree cannot find a move that
beats this value then we keep it as the value of the node.  This is
because the capture tree does not consider all moves and so may make us
believe that a position is bad when in fact we may have achieved a better
score for the position by making a move other than those considered in
the capture tree.  This 'other move' is represented here as a null-move.
We then generate our set of capture moves.

If merit is not good enough to cause a cutoff then the null move is
represented by BestPath.Move[Depth].  From being set to 0 before the
consideration of all the generated moves.  If this is still 0 at the
end then this null move is assigned to the path at this depth and a
cutoff will occur at the next level up because no move will have been
good enough to increase Lowest (alpha).
**************************************************************************/

	  BestPath.Value=Path->Value;
	  BestPath.Move[Depth].From=0;
	  if (BestPath.Value>Lowest) Lowest=BestPath.Value;
	  for (move=&Moves[Depth][1]; move<=&Moves[Depth][NumberOfMoves] && !ExitCode; move++) 
	  {
			if (MakeMove(Position, *move, NewPosition[Depth])) 
			{
			  Legal=TRUE;
			  Quiesce(NewPosition[Depth], Depth+1, -Highest, -Lowest, &NewPath, ExtendDepth, CheckExtends, false);
			  ReverseNewPathValue;
			  if (NewPath.Value>=Highest) {
				  memcpy(Path, &NewPath, SIZEOFPATH);
				  Path->Move[Depth]=*move;
				  return;
			  }
			  if (NewPath.Value>BestPath.Value) {
				  memcpy(&BestPath, &NewPath, SIZEOFPATH);
				  BestPath.Move[Depth]=*move;
				  if (NewPath.Value>Lowest) Lowest=NewPath.Value;
			  }
			} /* MakeMove */
	  } /* for */

 int NumCheckMoves = 0;

#ifdef USINGALLMOVESINQUIESCE
#ifdef USINGALLCHECKINGMOVESINQUIESCE
	  if (!All && CheckExtends < MAXCHECKEXTENDSINQUIESCE)
	  {
#ifdef TESTING
		  TotalQuiesceCheckCount++;
#endif
#ifdef LONG_CHECKING_IN_QUIESCE
		  NumberOfMoves=GetMoveList(Position, Moves[Depth]);
#else
		  NumberOfMoves=GetCheckMoveListWithoutCaptures(Position, Moves[Depth]);
#endif
		  if (NumberOfMoves > 1)
		  {
			//ShowPosition(Position);
		  }
		  for (move=&Moves[Depth][1]; move<=&Moves[Depth][NumberOfMoves] && !ExitCode; move++) 
		  {
#ifdef LONG_CHECKING_IN_QUIESCE
			if (move->Capture == EMPTY && MakeMove(Position, *move, NewPosition[Depth])) 
#else
			if (MakeMove(Position, *move, NewPosition[Depth])) 
#endif
			{
#ifdef LONG_CHECKING_IN_QUIESCE
#ifdef TESTING_CHECKING_MOVE_DETECTION
/*				bool b1 = IsCheckingMove(Position, *move);
				bool b2 = 1 == IsCheck(NewPosition[Depth]);

				if (b1 != b2)
				{
					ShowPosition(Position);
					ShowPosition(NewPosition[Depth]);
					b1 = IsCheckingMove(Position, *move);
					b2 = 1 == IsCheck(NewPosition[Depth]);
					assert(b1 == b2);
				}*/
#endif
//				if (IsCheckingMove(Position, *move))
				if (IsCheck(NewPosition[Depth]))
#endif
				{
				  if (++NumCheckMoves == 1)
				  {
					CheckExtends ++;
				  }
				  Quiesce(NewPosition[Depth], Depth+1, -Highest, -Lowest, &NewPath, ExtendDepth, CheckExtends, true);
				  ReverseNewPathValue;
				  if (NewPath.Value>=Highest) {
					  memcpy(Path, &NewPath, SIZEOFPATH);
					  Path->Move[Depth]=*move;
					  return;
				  }
				  if (NewPath.Value>BestPath.Value) {
					  memcpy(&BestPath, &NewPath, SIZEOFPATH);
					  BestPath.Move[Depth]=*move;
					  if (NewPath.Value>Lowest) Lowest=NewPath.Value;
				  }
				  if (NumCheckMoves > MAX_CHECKING_MOVES_ONE_PLY_IN_QUIESCE)
				   {
				  	break;
				  }
				}
			} /* MakeMove */
		  } /* for */
#ifdef TESTING
		  TotalQuiesceCheckCount++;
#endif
	  }
#endif
#endif

done:

	  // Can only be !Legal if using All=true moves
	  if (!Legal && !ExitCode)
	  {
		Path->Value=-10000;
	  }
	  else
	  {
#ifdef USEHASHINQUIESCE
	    //StoreHashMoveDetails(Position, 1, Flag, *BestPathMove, BestPath.Value);
#endif
		memcpy(Path, &BestPath, SIZEOFPATH);
	  }
}

int TSearcher::VerifyMove(TPosition Position, TMove Move)
{
	int Legal=TRUE;
	int Temp;
	TPosition NewPosition;
	memcpy(NewPosition, Position, SIZEOFPOSITION);
	if (NewPosition[MOVER]==WHITE && NewPosition[Move.From]>=EMPTY) Legal=FALSE;
	if (NewPosition[MOVER]==BLACK && NewPosition[Move.From]<=EMPTY) Legal=FALSE;
	if (Legal) {
		switch (NewPosition[Move.From]) 
		{
			case WP : Temp=Move.To-Move.From;
						 if (Temp==1 && Temp==-9 && Temp==11) Legal=FALSE;
						 if (GetY(Move.To)==8 && Move.PromotionPiece==EMPTY) Legal=FALSE;
						 break;
			case BP : Temp=Move.To-Move.From;
						 if (Temp==-1 && Temp==9 && Temp==-11) Legal=FALSE;
						 if (GetY(Move.To)==1 && Move.PromotionPiece==EMPTY) Legal=FALSE;
						 break;
			case WR : Legal=FALSE;
						 for (Temp=Move.From+10; Valid[Temp] && Position[Temp]>=EMPTY; Temp+=10) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From-10; Valid[Temp] && Position[Temp]>=EMPTY; Temp-=10) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From+1; Valid[Temp] && Position[Temp]>=EMPTY; Temp++) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From-1; Valid[Temp] && Position[Temp]>=EMPTY; Temp--) if (Temp==Move.To) Legal=TRUE;
						 break;
			case BR : Legal=FALSE;
						 for (Temp=Move.From+10; Valid[Temp] && Position[Temp]<=EMPTY; Temp+=10) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From-10; Valid[Temp] && Position[Temp]<=EMPTY; Temp-=10) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From+1; Valid[Temp] && Position[Temp]<=EMPTY; Temp++) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From-1; Valid[Temp] && Position[Temp]<=EMPTY; Temp--) if (Temp==Move.To) Legal=TRUE;
						 break;
			case WB : Legal=FALSE;
						 for (Temp=Move.From+9; Valid[Temp] && Position[Temp]>=EMPTY; Temp+=9) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From-9; Valid[Temp] && Position[Temp]>=EMPTY; Temp-=9) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From+11; Valid[Temp] && Position[Temp]>=EMPTY; Temp+=11) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From-11; Valid[Temp] && Position[Temp]>=EMPTY; Temp-=11) if (Temp==Move.To) Legal=TRUE;
						 break;
			case BB : Legal=FALSE;
						 for (Temp=Move.From+9; Valid[Temp] && Position[Temp]<=EMPTY; Temp+=9) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From-9; Valid[Temp] && Position[Temp]<=EMPTY; Temp-=9) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From+11; Valid[Temp] && Position[Temp]<=EMPTY; Temp+=11) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From-11; Valid[Temp] && Position[Temp]<=EMPTY; Temp-=11) if (Temp==Move.To) Legal=TRUE;
						 break;
			case WQ : Legal=FALSE;
						 for (Temp=Move.From+10; Valid[Temp] && Position[Temp]>=EMPTY; Temp+=10) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From-10; Valid[Temp] && Position[Temp]>=EMPTY; Temp-=10) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From+1; Valid[Temp] && Position[Temp]>=EMPTY; Temp++) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From-1; Valid[Temp] && Position[Temp]>=EMPTY; Temp--) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From+9; Valid[Temp] && Position[Temp]>=EMPTY; Temp+=9) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From-9; Valid[Temp] && Position[Temp]>=EMPTY; Temp-=9) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From+11; Valid[Temp] && Position[Temp]>=EMPTY; Temp+=11) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From-11; Valid[Temp] && Position[Temp]>=EMPTY; Temp-=11) if (Temp==Move.To) Legal=TRUE;
						 break;
			case BQ : Legal=FALSE;
						 for (Temp=Move.From+10; Valid[Temp] && Position[Temp]<=EMPTY; Temp+=10) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From-10; Valid[Temp] && Position[Temp]<=EMPTY; Temp-=10) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From+1; Valid[Temp] && Position[Temp]<=EMPTY; Temp++) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From-1; Valid[Temp] && Position[Temp]<=EMPTY; Temp--) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From+9; Valid[Temp] && Position[Temp]<=EMPTY; Temp+=9) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From-9; Valid[Temp] && Position[Temp]<=EMPTY; Temp-=9) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From+11; Valid[Temp] && Position[Temp]<=EMPTY; Temp+=11) if (Temp==Move.To) Legal=TRUE;
						 for (Temp=Move.From-11; Valid[Temp] && Position[Temp]<=EMPTY; Temp-=11) if (Temp==Move.To) Legal=TRUE;
						 break;
			case WN : Temp=abs(Move.From-Move.To);
						 if (Temp!=12 && Temp!=21 && Temp!=8 && Temp!=19) Legal=FALSE;
						 break;
			case BN : Temp=abs(Move.From-Move.To);
						 if (Temp!=12 && Temp!=21 && Temp!=8 && Temp!=19) Legal=FALSE;
						 break;
			case WK : Temp=abs(Move.From-Move.To);
						 if (Temp!=1 && Temp!=11 && Temp!=10 && Temp!=9 && !(Move.From==51 && (Move.To==31 || Move.To==71))) Legal=FALSE;
						 break;
			case BK : Temp=abs(Move.From-Move.To);
						 if (Temp!=1 && Temp!=11 && Temp!=10 && Temp!=9 && !(Move.From==58 && (Move.To==38 || Move.To==78))) Legal=FALSE;
						 break;
		}
	}
/*************************************************************************
Make move and check for check
**************************************************************************/
	NewPosition[Move.To]=NewPosition[Move.From];
	if (NewPosition[Move.To]==WP) {
		if (GetY(Move.To)==6 && GetX(Move.To)==NewPosition[ENPAWN]) NewPosition[Move.To-1]=EMPTY;
		if (GetY(Move.To)==8) NewPosition[Move.To]=Move.PromotionPiece;
	}
	if (NewPosition[Move.To]==BP) {
		if (GetY(Move.To)==3 && GetX(Move.To)==NewPosition[ENPAWN]) NewPosition[Move.To+1]=EMPTY;
		if (GetY(Move.To)==1) NewPosition[Move.To]=Move.PromotionPiece+100;
	}
	if (NewPosition[Move.From]==WK) {
		NewPosition[WKINGPOSITION]=Move.To;
		if (Move.From==51 && Move.To==71) {
			NewPosition[71]=WK;
			NewPosition[61]=WR;
			NewPosition[81]=EMPTY;
		}
		if (Move.From==51 && Move.To==31) {
			NewPosition[31]=WK;
			NewPosition[41]=WR;
			NewPosition[11]=EMPTY;
		}
	}
	if (NewPosition[Move.From]==BK) {
		NewPosition[BKINGPOSITION]=Move.To;
		if (Move.From==58 && Move.To==78) {
			NewPosition[78]=BK;
			NewPosition[68]=BR;
			NewPosition[88]=EMPTY;
		}
		if (Move.From==58 && Move.To==38) {
			NewPosition[38]=BK;
			NewPosition[48]=BR;
			NewPosition[18]=EMPTY;
		}
	}
	NewPosition[Move.From]=EMPTY;
	if (IsCheck(NewPosition)) Legal=FALSE;
	return Legal;
}

void
TSearcher::TranslateMove(TMove mv, char* s)
{
			sprintf_s(s, 5, "%c%c%c%c ",
					(char)(GetFile[mv.From]+'a'-1),
					(char)(GetRank[mv.From]+'0'),
					(char)(GetFile[mv.To]+'a'-1),
					(char)(GetRank[mv.To]+'0'));
}

void
TSearcher::Minimax(TPosition Position, int Depth, int Lowest, int Highest, TPath* Path, int LocalFinalDepth, bool VerifyNullMove)
{
	if (ExitCode!=0) return;

	int ExtendDepth = (LocalFinalDepth-FinalDepth);
/*************************************************************************
Do we want to extend?
**************************************************************************/
	if (ExtendDepth<MaxExtensions) 
	{
		if	(UsePawnPushExtensions && 
			( 
				(Position[LastMove[Depth-1].To]==WP && GetY(LastMove[Depth-1].To)>=6 && GetY(LastMove[Depth-1].To)<8) ||
				(Position[LastMove[Depth-1].To]==BP && GetY(LastMove[Depth-1].To)<=3 && GetY(LastMove[Depth-1].To)>1 ) 
			) 
			)
		{
#ifdef TESTING
			PawnPushExtensionsCount ++;
#endif
			ExtendDepth+=EXTENDPLY;
		}
		else if (UseCheckExtensions && IsCheck(Position)) 
		{
			ExtendDepth+=EXTENDPLY;
#ifdef TESTING
				CheckExtensionsCount ++;
#endif
		}
	}
	LastMove[Depth].From=0;

/*************************************************************************
If this is a terminal node then evaluate using the static-evaluation
function.
**************************************************************************/

	if (Depth>=FinalDepth+ExtendDepth) 
	{
		Quiesce(Position, Depth, Lowest, Highest, Path, ExtendDepth, 0, false);
		Path->Move[Depth].From=0;
		return;
	}
#ifdef COUNTNODESINMINIMAX
	CurrentPathNodes++;
#endif
	TMove* move;
	int MoveCount=0;
	int NumberOfMoves, Flag;
	TPath BestPath;
	TMove* BestPathMove=&BestPath.Move[Depth];
	BestPathMove->From=0;
	POSITIONELEMENT* NewPositionPointer=NewPosition[Depth];
	TPath NewPath;
	int Height=0;
	GlobalHashMove.From=BestPathMove->From=0;
	GetHashMoveDetails(Position, Height, Flag, *BestPathMove, BestPath.Value);
	if (Height>0 && BestPathMove->From!=0) 
	{
#ifdef TESTING
		if (!VerifyMove(Position, *BestPathMove)) 
		{
			UnverifiedHashEntries++;
			Height=0;
		}
#endif
		if (Height>0) GlobalHashMove=*BestPathMove;
		if (Height>=(FinalDepth+ExtendDepth-Depth)/* || (Flag==VALID && BestPath.Value>=MinimumMate)*/) {
#ifdef TESTING
			HashSuccessCount++;
			if (IsAlwaysReplaceRetrieval)
			{
				AlwaysReplaceHashSuccessCount ++;
			}
			else
			{
				DepthHashSuccessCount ++;
			}
#endif
			if (Flag==VALID) 
			{
				Path->Move[Depth]=*BestPathMove;
				Path->Move[Depth].Capture=Position[BestPathMove->To];
				Path->Move[Depth+1].From=0;
				Path->Value=BestPath.Value;
				return;
			}
			if (Flag==UBOUND && BestPath.Value<Highest) 
			{
				Highest=BestPath.Value;
			}
			if (Flag==LBOUND && BestPath.Value>Lowest) 
			{
				Lowest=BestPath.Value;
			}
			if (Lowest>=Highest) 
			{
				Path->Move[Depth]=*BestPathMove;
				Path->Move[Depth].Capture=Position[BestPathMove->To];
				Path->Move[Depth+1].From=0;
				Path->Value=BestPath.Value;
				UPDATEHISTORY(Path->Move[Depth].From, Path->Move[Depth].To);
				return;
			}
		}
	}

	// Fail-High Reductions
	// If this is during a minimal window search...
	BestPath.Value=LowEval;

	int FailHigh=0;

	int ReduceDueToNullMove = 0;
#ifndef NEWFAILHIGHCODE
	if (UseFailHighReductions && Depth+1 < FinalDepth+ExtendDepth && !IsCheck(Position) && LastMove[Depth-1].Capture==EMPTY) 
	{
		if (Evaluate(Position, Lowest, Highest) >= Highest + FAILHIGHERROR) 
		{
			FailHigh=1;
#ifdef TESTING
			FailHighReductionsCount ++;
#endif
		}
	} 
#endif

	// Null Move?
	// Not when searching Principal Variation
	// Not when in check
	// Not if nearly at the leaf nodes

	int DepthRemaining = (FinalDepth + ExtendDepth) - Depth;
	if (UseNullMove && ((Depth+1)<(FinalDepth+ExtendDepth)) && !IsCheck(Position)) 
	{
#ifdef TESTING
		NullMoveAttemptsCount++;
#endif
		// Not if previous move was a null move
		//if (LastMove[Depth-1].From!=0) 
		{
			int NullMoveReduceDepth = DEFAULT_NULL_MOVE_REDUCE_DEPTH;

			if (DepthRemaining >= 6)
			{
				NullMoveReduceDepth += (DepthRemaining - 5);
			}

			int Pieces;
			if (Position[MOVER]==WHITE) 
			{
				Pieces=Position[WHITEQUEENS]+Position[WHITEKNIGHTS]+Position[WHITEBISHOPS]+Position[WHITEROOKS];
			} else {
				Pieces=Position[BLACKQUEENS]+Position[BLACKKNIGHTS]+Position[BLACKBISHOPS]+Position[BLACKROOKS];
			}
			// Not if not many pieces left for the side to move
#ifndef VERIFIEDNULLMOVE
			if (Pieces>NullMoveStopMaterial) 
#endif
			{
#ifndef NOZORBRIST
				int HashKey=Position[HASHKEYFIELD1];
				int OrigHashKey=HashKey;
#endif
				int EnPawn=Position[ENPAWN];
#ifndef NOZORBRIST
				HashKey^=PieceSquareValues[0][1];
				HashKey^=PieceSquareValues[0][0];
				Position[HASHKEYFIELD1]=HashKey;
#endif
				// Make the null move
				Position[MOVER]=(Position[MOVER]==WHITE ? BLACK : WHITE);
				Position[ENPAWN]=0;
				Path->Move[Depth].From=0;
				Path->Move[Depth+1].From=0;
				// Pass down a minimal window, if the next search can't get
				// a value at least of at least -Highest, then it has failed high
				// here because the value will be >Highest, which means the
				// null move is good enough to cause a cut off.
				// With this, we assume that the best real move in this position
				// must be better than the null move and would therefore also
				// cause a cut-off.
				Minimax(Position, Depth+NullMoveReduceDepth+1, -Highest, -Highest+1, &NewPath, FinalDepth+ExtendDepth-FailHigh, VerifyNullMove);
#ifndef NOZORBRIST
				Position[HASHKEYFIELD1]=OrigHashKey;
#endif
				Position[MOVER]=(Position[MOVER]==WHITE ? BLACK : WHITE);
				Position[ENPAWN]=EnPawn;
				ReverseNewPathValue;
				if (NewPath.Value>=Highest) 
				{
#ifdef VERIFIEDNULLMOVE
					if (VerifyNullMove)
					{
#ifdef TESTING
					NullMoveReductionsCount++;
#endif				
						VerifyNullMove = false;
						ReduceDueToNullMove = 1;
					}
					else
					{
#ifdef TESTING
					NullMoveCutoffsCount++;
#endif				
					Path->Value=NewPath.Value;
					//StoreHashMoveDetails(Position, FinalDepth+ExtendDepth-Depth-NullMoveReduceDepth-FailHigh, LBOUND, *BestPathMove, BestPath.Value);
					return;
					}
#else
#ifdef TESTING
					NullMoveCutoffsCount++;
#endif				
					Flag=LBOUND;
					Path->Value=NewPath.Value;
					BestPath.Value=NewPath.Value;
					BestPathMove->From=0;
					StoreHashMoveDetails(Position, FinalDepth+ExtendDepth-Depth-NullMoveReduceDepth, LBOUND, *BestPathMove, BestPath.Value);
					return;
#endif
				} 
			}
		}
	} // Null Move
	Flag=UBOUND;

	CurrentDepth=Depth;
	NumberOfMoves=GetMoveList(Position, Moves[Depth]);

	int CurrentPositionIsCheck = IsCheck(Position);

research:
	bool foundPVNode = false;
	for (move=&Moves[Depth][1]; move<=&Moves[Depth][NumberOfMoves] && !ExitCode; move++) 
	{
		if (MakeMove(Position, *move, NewPositionPointer)) 
		{
#ifdef NEWFAILHIGHCODE
			// New Fail High Reduction Code
			if (move->Capture == EMPTY && !CurrentPositionIsCheck && UseFailHighReductions && Depth+1 < FinalDepth+ExtendDepth)
			{
				if (!IsCheck(*NewPosition))
				{
					if (Evaluate(Position, Lowest, Highest) >= Highest + FAILHIGHERROR) 
					{
						FailHigh=1;
#ifdef TESTING
						FailHighReductionsCount ++;
#endif
					}
				}
			}
#endif

			MoveCount++;
#ifdef FUTILITYPRUNING
			int Eval = FastEvaluate(Position, Lowest, Highest);
			if (Depth+1 >= FinalDepth+ExtendDepth && move->Capture == EMPTY && !CurrentPositionIsCheck  && !IsCheck(*NewPosition))
			{
				if (Eval + FUTILITYMARGIN1 < Lowest) 
				{
#ifdef TESTING
					FutilityPrunes1Count++;
#endif
					continue;
				}
			}
			else if (Depth+2 >= FinalDepth+ExtendDepth && move->Capture == EMPTY && !CurrentPositionIsCheck  && !IsCheck(*NewPosition))
			{
				if (Eval + FUTILITYMARGIN2 < Lowest) 
				{
#ifdef TESTING
					FutilityPrunes2Count++;
#endif
					continue;
				}
			}
#endif
/*************************************************************************
Draw?
**************************************************************************/
			if (Depth==1) 
			{
				CurrentDepth=Depth;
				if (PreviousPosition(*move)) 
				{
					NewPath.Value=-Contempt;
					NewPath.Move[Depth+1].From=0;
					goto DrawJump;
				}
			}
			LastMove[Depth]=*move;
			if (foundPVNode) 
			{
				// Minimal Window Search
				Minimax(NewPositionPointer, Depth+1, -Lowest-1, -Lowest, &NewPath, FinalDepth+ExtendDepth-FailHigh-ReduceDueToNullMove, VerifyNullMove);
				ReverseNewPathValue;
				if (NewPath.Value>Lowest && NewPath.Value<Highest) 
				{
					Minimax(NewPositionPointer, Depth+1, -Highest, -Lowest, &NewPath, FinalDepth+ExtendDepth-FailHigh-ReduceDueToNullMove, VerifyNullMove);
					ReverseNewPathValue;
				}
			} 
			else 
			{
				Minimax(NewPositionPointer, Depth+1, -Highest, -Lowest, &NewPath, FinalDepth+ExtendDepth-FailHigh-ReduceDueToNullMove, VerifyNullMove);
				ReverseNewPathValue;
			}
DrawJump:
			if (NewPath.Value>=Highest) 
			{
				if (NewPath.Value>9000) 
				{
					Flag=VALID; 
				}
				else
				{
					Flag=LBOUND;
				}
				memcpy(Path, &NewPath, SIZEOFPATH);
				Path->Move[Depth]=*BestPathMove=*move;
				BestPath.Value=NewPath.Value;
				UPDATEHISTORY(Path->Move[Depth].From, Path->Move[Depth].To);
				goto done;
			}
			if (NewPath.Value>BestPath.Value) 
			{
				memcpy(&BestPath, &NewPath, SIZEOFPATH);
				*BestPathMove=*move;
				if (NewPath.Value>Lowest) 
				{
					Flag=VALID;
					Lowest=NewPath.Value;
					foundPVNode = true;
				}
			}
		} /* MakeMove */
	}

#ifdef VERIFIEDNULLMOVE
     /* if there is a fail-high report, but no cutoff was found, the position
     * is a zugzwang and has to be re-searched with the original depth */
	if (ReduceDueToNullMove && BestPath.Value < Highest)
	{
#ifdef TESTING
		ZugzwangCount++;
#endif
		ReduceDueToNullMove = 0;
		VerifyNullMove = true;
		goto research;
	}
#endif
	if (MoveCount==0) 
	{
		switch (WinnerWhenNoMoves(Position)) 
		{
				case 1 : Path->Value=10000; break;
				case 0 : Path->Value=0; break;
				case -1 : Path->Value=-10000; break;
				default : exit(0);
		}
		Path->Move[Depth].From=0;
		BestPathMove->From=0;
		BestPath.Value=Path->Value;
		Flag=VALID;
		goto done;
	}

	memcpy(Path, &BestPath, SIZEOFPATH);
done:
	if (ExitCode==0) 
	{
		//StoreHashMoveDetails(Position, FinalDepth+ExtendDepth-Depth-FailHigh-ReduceDueToNullMove, Flag, *BestPathMove, BestPath.Value);
		StoreHashMoveDetails(Position, FinalDepth+ExtendDepth-Depth, Flag, *BestPathMove, BestPath.Value);
	}
}

void TSearcher::GetSimpleMoveString(TMove move, char* moveString)
{
	if (move.PromotionPiece==EMPTY) 
	{
		sprintf_s( moveString, 5, "%c%c%c%c",
			GetX(move.From)+'a'-1,
			GetY(move.From)+'0',
			GetX(move.To)+'a'-1,
			GetY(move.To)+'0' );
	} 
	else 
	{
		char Promote;
		switch (move.PromotionPiece%100) 
		{
			case QUEEN : Promote='q'; break;
			case KNIGHT : Promote='n'; break;
			case BISHOP : Promote='b'; break;
			case ROOK : Promote='r'; break;
		}
		sprintf_s( moveString, 6, "%c%c%c%c%c",
			GetX(move.From)+'a'-1,
			GetY(move.From)+'0',
			GetX(move.To)+'a'-1,
			GetY(move.To)+'0',
			Promote );
	}
}

void
TSearcher::WriteCurrentMoveToGUI(int MoveNumber)
{
#ifndef TESTING
	if (FinalDepth < WRITE_CURRENT_MOVE_MINIMUM_DEPTH)
	{
		return;
	}
	TMove move = CurrentDepthZeroMove;
	char moveString[7];
	GetSimpleMoveString(move, moveString);

	cout << "info currmove " << moveString << " currmovenumber " << MoveNumber << COMMAND_ENDL;

#ifdef LOG_COMMUNICATIONS
#ifdef LOG_VERBOSE_COMMUNICATIONS
	std::ofstream out(LOG_FILE, ios_base::app);
	out << "info currmove " << moveString << " currmovenumber " << MoveNumber << LOG_ENDL;
	out.close();
#endif
#endif

	fflush(stdout);
#endif
}

void
TSearcher::WritePrincipalPathToGUI()
{
	if (FinalDepth < WRITE_PV_MINIMUM_DEPTH)
	{
		return;
	}
	timeticker=GetTickCount();
	int elapsed = timeticker - searchStartTime;
	if (elapsed < 1000)
	{
		elapsed = 1000;
	}
	int nps = CurrentPathNodes / (elapsed / 1000);

	cout << "info depth " << FinalDepth << " nodes " << CurrentPathNodes << " nps " << nps;
	cout << " pv ";
	int i = 0;
	char moveString[7];

	while (PrincipalPath.Move[i].From != 0)
	{
		GetSimpleMoveString(PrincipalPath.Move[i], moveString);
		cout << moveString << " ";
		i++;
	}
	cout << "score cp " << PrincipalPath.Value;
	cout << COMMAND_ENDL;

	fflush(stdout);

#ifdef LOG_COMMUNICATIONS
#ifdef LOG_VERBOSE_COMMUNICATIONS
	std::ofstream out(LOG_FILE, ios_base::app);
	out << "info depth " << FinalDepth << " nodes " << CurrentPathNodes << " nps " << nps;
	out << " pv ";
	i = 0;

	while (PrincipalPath.Move[i].From != 0)
	{
		GetSimpleMoveString(PrincipalPath.Move[i], moveString);
		out << moveString << " ";
		i++;
	}
	out << "score cp " << PrincipalPath.Value;
	out << LOG_ENDL;
	out.close();
#endif
#endif
}

void
TSearcher::MinimaxZero(TPosition Position, unsigned int Depth, int Lowest, int Highest, TPath* Path, unsigned int ExtendDepth)
{
	if (ExitCode!=0) return;
	LastMove[Depth].From=0;
	CurrentPathNodes++;
	TMove* move;
	int MoveCount=0;
	int Flag;
	TPath BestPath;
	TMove* BestPathMove=&BestPath.Move[Depth];
	BestPathMove->From=0;
	POSITIONELEMENT* NewPositionPointer=NewPosition[Depth];
	TPath NewPath;

	bool VerifyNullMove = true;

	BestPath.Value=LowEval;

	Flag=UBOUND;
	for (move=&Moves[Depth][1]; move<=&Moves[Depth][Depth0Amount] && !ExitCode; move++) {
		if (MakeMove(Position, *move, NewPositionPointer)) {
			CurrentDepthZeroMove=*move;

			WriteCurrentMoveToGUI(MoveCount + 1);

/*************************************************************************
Draw?
**************************************************************************/
			MoveCount++;
			CurrentDepth=Depth;
			if (PreviousPosition(*move)) 
			{
				 NewPath.Value=Contempt;
				 NewPath.Move[Depth+1].From=0;
				 goto DrawJump;
			}
			LastMove[Depth]=*move;
			if (MoveCount>1 && UseMinimalWindow) 
			{
				Minimax(NewPositionPointer, Depth+1, -Lowest-1, -Lowest, &NewPath, FinalDepth, VerifyNullMove);
				ReverseNewPathValue;
				if (NewPath.Value>Lowest && NewPath.Value<Highest) 
				{
					  Minimax(NewPositionPointer, Depth+1, -Highest, -Lowest, &NewPath, FinalDepth, VerifyNullMove);
					  ReverseNewPathValue;
				}
			} else {
				Minimax(NewPositionPointer, Depth+1, -Highest, -Lowest, &NewPath, FinalDepth, VerifyNullMove);
				ReverseNewPathValue;
			}
DrawJump:
			move->Score=NewPath.Value;
			if (NewPath.Value>=Highest) {
				Flag=LBOUND;
				memcpy(Path, &NewPath, SIZEOFPATH);
				Path->Move[Depth]=*BestPathMove=*move;
				BestPath.Value=NewPath.Value;
				UPDATEHISTORY(Path->Move[Depth].From, Path->Move[Depth].To);
				goto done;
			}
			if (NewPath.Value>BestPath.Value) {
				memcpy(&BestPath, &NewPath, SIZEOFPATH);
				*BestPathMove=*move;
				if (NewPath.Value>Lowest) {
				  Flag=VALID;
				  Lowest=NewPath.Value;
				  if (ExitCode==0) {
					  memcpy(&PrincipalPath, &BestPath, SIZEOFPATH);
					  PrincipalPath.Depth=FinalDepth+ExtendDepth;
					  Satisfied=(PrincipalPath.Value>=(PIBest-SATISFACTION))
						&& PrincipalPath.Value>ValueGuess-SATISFACTION;
					  if (PrincipalPath.Value>MinimumMate) ExitWithMove();
				  }
				}
				WritePrincipalPathToGUI();
			}
		} /* MakeMove */
	}
	memcpy(Path, &BestPath, SIZEOFPATH);
done:
	if (PrincipalPath.Value>=StopScore &&
			PrincipalPath.Move[0].From==StopMove.From &&
			PrincipalPath.Move[0].To==StopMove.To) ExitWithMove();
#ifdef HASHTABLE
	if (/*BestPath.Value<9000 && BestPath.Value>-9000 && */ExitCode==0) {
		  StoreHashMoveDetails(Position, FinalDepth+ExtendDepth-Depth, Flag, *BestPathMove, BestPath.Value);
	}
#endif
}

void
TSearcher::ReOrderMoves(TMoveArray Moves, int Amount)
{
	TMove TempMove;
	int i, x;
	for (i=1; i<=Amount-1; i++)
		for (x=i+1; x<=Amount; x++)
			if (Moves[x].Score>Moves[i].Score) {
				TempMove=Moves[i];
				Moves[i]=Moves[x];
				Moves[x]=TempMove;
			}
}

void
TSearcher::SetUseHistory(int use)
{
	UseHistory=use;
}

void
TSearcher::SetUseNullMove(int use)
{
	UseNullMove=use;
}

void
TSearcher::SetUseFailHighReductions(int use)
{
	UseFailHighReductions=use;
}

void
TSearcher::SetContempt(int contempt)
{
	Contempt=contempt;
}

void
TSearcher::SetUseMinimalWindow(int useminwin)
{
	UseMinimalWindow=useminwin;
}

void
TSearcher::SetInitialPosition(TChessBoard NewPosition)
{
#ifdef VERBOSE_LOGGING
	sprintf_s(logtextsearcher, LOGTEXTSIZE, "Inside SetInitialPosition function");
	WriteLog(logtextsearcher);
#endif
	int i, x, y;
	POSITIONELEMENT Square;
	if (MinimumMate>9000) {
		if ((NewPosition.LastMoveMade()-LastMoveNumber)!=2) {
			MinimumMate=9000;
		}
	}
	LastMoveNumber=NewPosition.LastMoveMade();
	for (i=0; i<89; i++)
		StartPosition[i]=NewPosition.GetSquare(i);
	StartPosition[WHITEPAWNS]=
	StartPosition[WHITEKNIGHTS]=
	StartPosition[WHITEBISHOPS]=
	StartPosition[WHITEQUEENS]=
	StartPosition[WHITEROOKS]=
	StartPosition[WHITEKINGS]=
	StartPosition[BLACKPAWNS]=
	StartPosition[BLACKKNIGHTS]=
	StartPosition[BLACKBISHOPS]=
	StartPosition[BLACKQUEENS]=
	StartPosition[BLACKROOKS]=
	StartPosition[BLACKKINGS]=0;

#ifdef VERBOSE_LOGGING
	sprintf_s(logtextsearcher, LOGTEXTSIZE, "About to loop");
	WriteLog(logtextsearcher);
#endif

	for (x=1; x<=8; x++) {
	  for (y=1; y<=8; y++) {
		 Square=x*10+y;
		 if (StartPosition[Square]==WK) {
			  StartPosition[WKINGPOSITION]=Square;
			  StartPosition[WHITEKINGS]++;
			  StartPosition[WHITEKINGS+StartPosition[WHITEKINGS]]=Square;
		 }
		 if (StartPosition[Square]==BK) {
			  StartPosition[BKINGPOSITION]=Square;
			  StartPosition[BLACKKINGS]++;
			  StartPosition[BLACKKINGS+StartPosition[BLACKKINGS]]=Square;
		 }
		 if (StartPosition[Square]==WP) {
			  StartPosition[WHITEPAWNS]++;
			  StartPosition[WHITEPAWNS+StartPosition[WHITEPAWNS]]=Square;
		 }
		 if (StartPosition[Square]==BP) {
			  StartPosition[BLACKPAWNS]++;
			  StartPosition[BLACKPAWNS+StartPosition[BLACKPAWNS]]=Square;
		 }
		 if (StartPosition[Square]==WB) {
			  StartPosition[WHITEBISHOPS]++;
			  StartPosition[WHITEBISHOPS+StartPosition[WHITEBISHOPS]]=Square;
		 }
		 if (StartPosition[Square]==BB) {
			  StartPosition[BLACKBISHOPS]++;
			  StartPosition[BLACKBISHOPS+StartPosition[BLACKBISHOPS]]=Square;
		 }
		 if (StartPosition[Square]==WN) {
			  StartPosition[WHITEKNIGHTS]++;
			  StartPosition[WHITEKNIGHTS+StartPosition[WHITEKNIGHTS]]=Square;
		 }
		 if (StartPosition[Square]==BN) {
			  StartPosition[BLACKKNIGHTS]++;
			  StartPosition[BLACKKNIGHTS+StartPosition[BLACKKNIGHTS]]=Square;
		 }
		 if (StartPosition[Square]==WQ) {
			  StartPosition[WHITEQUEENS]++;
			  StartPosition[WHITEQUEENS+StartPosition[WHITEQUEENS]]=Square;
		 }
		 if (StartPosition[Square]==BQ) {
			  StartPosition[BLACKQUEENS]++;
			  StartPosition[BLACKQUEENS+StartPosition[BLACKQUEENS]]=Square;
		 }
		 if (StartPosition[Square]==WR) {
			  StartPosition[WHITEROOKS]++;
			  StartPosition[WHITEROOKS+StartPosition[WHITEROOKS]]=Square;
		 }
		 if (StartPosition[Square]==BR) {
			  StartPosition[BLACKROOKS]++;
			  StartPosition[BLACKROOKS+StartPosition[BLACKROOKS]]=Square;
		 }
	  }
	}
	StartPosition[LASTMOVESQUARE]=0;
	TMoveList MoveList=NewPosition.GetPreviousMoves();
	StartPosition[WHITECASTLED]=FALSE;
	StartPosition[BLACKCASTLED]=FALSE;
	for (i=1; i<=MoveList.Amount; i++) {
		if ((MoveList.Moves[i].From==51 && MoveList.Moves[i].To==71) ||
			(MoveList.Moves[i].From==51 && MoveList.Moves[i].To==31))
				StartPosition[WHITECASTLED]=TRUE;
		if ((MoveList.Moves[i].From==58 && MoveList.Moves[i].To==78) ||
			(MoveList.Moves[i].From==58 && MoveList.Moves[i].To==38))
				StartPosition[BLACKCASTLED]=TRUE;
	}
#ifdef VERBOSE_LOGGING
	sprintf_s(logtextsearcher, LOGTEXTSIZE, "Computing hash key");
	WriteLog(logtextsearcher);
#endif

#ifndef NOZORBRIST
	int HashKey = ComputeHashKey(StartPosition);
#ifdef CHARPOSITION
	StartPosition[HASHKEYFIELD1]=HashKey/HASHDIV3;
	StartPosition[HASHKEYFIELD2]=HashKey%HASHDIV3/HASHDIV2;
	StartPosition[HASHKEYFIELD3]=HashKey%HASHDIV2/HASHDIV1;
	StartPosition[HASHKEYFIELD4]=HashKey%HASHDIV1;
#else
	StartPosition[HASHKEYFIELD1]=HashKey;
#endif
#endif

#ifdef VERBOSE_LOGGING
	sprintf_s(logtextsearcher, LOGTEXTSIZE, "Checking positions for repeats");
	WriteLog(logtextsearcher);
#endif

	TMoveArray Moves;
	int Identical;
	int DrawCount=0;
	int Ply1DrawCount=0;
	TPosition TempPosition;
	int MovesMade=NewPosition.LastMoveMade();
	CurrentDepth=0;
	int Amount=GetMoveList(StartPosition, Moves);
	int j;
	int LastChange=0;
	DrawMoves[0].From=0;
	Ply1DrawMovesPly0[0].From=0;
/* Set LastChange=Number of last capturing move */
	for (j=1; j<=MovesMade; j++) {
		if (NewPosition.MovesMade[j].Capture!=EMPTY || NewPosition.MovesMade[j].Score==TRUE)
			LastChange=j;
	}
	for (i=1; i<=Amount; i++) {
		if (MakeMove(StartPosition, Moves[i], TempPosition)) {
			NewPosition.TakeBackAllMoves();
/* Replay all moves up to the Last Change */
			for (j=1; j<=LastChange; j++) NewPosition.ReplayMove();
			for (j=LastChange; j<MovesMade; j++) {
				Identical=TRUE;
				for (x=0; x<=6; x++)
					if (NewPosition.GetSquare(x)!=TempPosition[x]) Identical=FALSE;
				if (Identical)
				for (x=1; x<=8 && Identical; x++)
					for (y=1; y<=8 && Identical; y++)
					  if (NewPosition.GetSquare(x*10+y)!=TempPosition[x*10+y]) Identical=FALSE;
				if (Identical) {
				  DrawMoves[DrawCount]=Moves[i];
				  DrawCount++;
				  if (DrawCount>24) DrawCount=24;
				  break;
				}
/* Test TempPosition2 which represents what position opponent can bring about */
				TMoveArray Moves2;
				TPosition TempPosition2;
				int Amount2=GetMoveList(TempPosition, Moves2);
				for (int k=1; k<=Amount2; k++) {
				  if (MakeMove(TempPosition, Moves2[k], TempPosition2)) {
					 Identical=TRUE;
					 for (x=0; x<=6; x++)
						if (NewPosition.GetSquare(x)!=TempPosition2[x]) Identical=FALSE;
					 if (Identical)
					 for (x=1; x<=8 && Identical; x++)
						for (y=1; y<=8 && Identical; y++)
						  if (NewPosition.GetSquare(x*10+y)!=TempPosition2[x*10+y]) Identical=FALSE;
					 if (Identical) {
						Ply1DrawMovesPly0[Ply1DrawCount]=Moves[i];
						Ply1DrawMovesPly1[Ply1DrawCount]=Moves2[k];
						Ply1DrawCount++;
						if (Ply1DrawCount>24) Ply1DrawCount=24;
						break;
					 }
				  }
				}
				NewPosition.ReplayMove();
			}
		}
	}
	DrawMoves[DrawCount].From=0;
	Ply1DrawMovesPly0[Ply1DrawCount].From=0;

#ifdef VERBOSE_LOGGING
	sprintf_s(logtextsearcher, LOGTEXTSIZE, "Finalising");
	WriteLog(logtextsearcher);
#endif

	for (i=0; i<89; i++)
	{
   		PathBoard[i]=StartPosition[i];
	}
}

bool
TSearcher::IsWhiteToMove()
{
	return StartPosition[MOVER] == WHITE;
}

int
TSearcher::MakeMove(TPosition Position, TMove& Move, TPosition NewPosition)
{
	int TypeIndex, PieceIndex;
	memcpy(NewPosition, Position, SIZEOFPOSITION);
/*************************************************************************
First we make the move.  In the rest of the function we will modify the
new position if required, (castling, promotion, en-passant, for example).
**************************************************************************/
	POSITIONELEMENT *FromPiece=Position+Move.From;
	POSITIONELEMENT *ToPiece=Position+Move.To;
#ifndef NOZORBRIST
#ifdef CHARPOSITION
	int HashKey=Position[HASHKEYFIELD1]*HASHDIV3+Position[HASHKEYFIELD2]*HASHDIV2+Position[HASHKEYFIELD3]*HASHDIV1+Position[HASHKEYFIELD4];
#else
	int HashKey=Position[HASHKEYFIELD1];
#endif
#ifdef HASHCHECK
	int OrigKey=HashKey;
#endif
	int White=*FromPiece<EMPTY;
#endif
	NewPosition[Move.To]=*FromPiece;
#ifndef NOZORBRIST
	HashKey^=PieceSquareValues[Move.From][*FromPiece-(White ? 1 : 95)];
#endif
/*************************************************************************
For display purposes (when showing the path), we update the CapturePiece
field of the move structure.  Also we update the Piece Value fields
of the position.
**************************************************************************/
	if (*ToPiece!=EMPTY) {
#ifndef NOZORBRIST
		if (*ToPiece>EMPTY) {
			HashKey^=PieceSquareValues[Move.To][*ToPiece-95];
		} else {
			HashKey^=PieceSquareValues[Move.To][*ToPiece-1];
		}
#endif
		Move.Capture=*ToPiece;
	} else
		Move.Capture=EMPTY;
#ifndef NOZORBRIST
	HashKey^=PieceSquareValues[Move.To][*FromPiece-(White ? 1 : 95)];
#endif
	NewPosition[Move.From]=EMPTY;
/*************************************************************************
For kings, we need to make alterations for castling moves and also we need
to update the NewPosition[xKINGPOSITION] values.  Also we flag that the
king has moved to avoid future castling.
**************************************************************************/
	if (*FromPiece==WK) {
		NewPosition[WKINGPOSITION]=Move.To;
		NewPosition[WKINGMOVED]=TRUE;
		if (Move.From==51 && Move.To==31) {
			NewPosition[41]=WR;
			NewPosition[11]=EMPTY;
			NewPosition[WHITECASTLED]=TRUE;
#ifndef NOZORBRIST
			HashKey^=PieceSquareValues[11][WR-1];
			HashKey^=PieceSquareValues[41][WR-1];
#endif
		}
		if (Move.From==51 && Move.To==71) {
			NewPosition[61]=WR;
			NewPosition[81]=EMPTY;
			NewPosition[WHITECASTLED]=TRUE;
#ifndef NOZORBRIST
			HashKey^=PieceSquareValues[81][WR-1];
			HashKey^=PieceSquareValues[61][WR-1];
#endif
		}
	}
	if (*FromPiece==BK) {
		NewPosition[BKINGPOSITION]=Move.To;
		NewPosition[BKINGMOVED]=TRUE;
		if (Move.From==58 && Move.To==38) {
			NewPosition[48]=BR;
			NewPosition[18]=EMPTY;
			NewPosition[BLACKCASTLED]=TRUE;
#ifndef NOZORBRIST
			HashKey^=PieceSquareValues[18][BR-95];
			HashKey^=PieceSquareValues[48][BR-95];
#endif
		}
		if (Move.From==58 && Move.To==78) {
			NewPosition[68]=BR;
			NewPosition[88]=EMPTY;
			NewPosition[BLACKCASTLED]=TRUE;
#ifndef NOZORBRIST
			HashKey^=PieceSquareValues[88][BR-95];
			HashKey^=PieceSquareValues[68][BR-95];
#endif
		}
	}
/*************************************************************************
For pawns, we need to make alterations for promotions and en-passant moves.
**************************************************************************/
	if (*FromPiece==WP) {
	  if (GetRank[Move.To]==8) {
		  NewPosition[Move.To]=Move.PromotionPiece;
#ifndef NOZORBRIST
		  HashKey^=PieceSquareValues[Move.To][WP-1];
		  HashKey^=PieceSquareValues[Move.To][Move.PromotionPiece-1];
#endif
	  }
	  if ((Move.From-Move.To==-11 || Move.From-Move.To==9) && *ToPiece==EMPTY) {
		  NewPosition[Move.To-1]=EMPTY;
#ifndef NOZORBRIST
		  HashKey^=PieceSquareValues[Move.To-1][BP-95];
#endif
		  Move.Capture=BP;
	  }
	}
	if (*FromPiece==BP) {
	  if (GetRank[Move.To]==1) {
		  NewPosition[Move.To]=Move.PromotionPiece+100;
#ifndef NOZORBRIST
		  HashKey^=PieceSquareValues[Move.To][BP-95];
		  HashKey^=PieceSquareValues[Move.To][Move.PromotionPiece+5];
#endif
	  }
	  if ((Move.From-Move.To==11 || Move.From-Move.To==-9) && *ToPiece==EMPTY) {
		  NewPosition[Move.To+1]=EMPTY;
#ifndef NOZORBRIST
		  HashKey^=PieceSquareValues[Move.To+1][WP-1];
#endif
		  Move.Capture=WP;
	  }
	}
/*************************************************************************
For rooks, we need to flag their movements for castling privelege purposes.
**************************************************************************/
	if (Move.From==11 || Move.To==11) NewPosition[WROOK1MOVED]=TRUE;
	if (Move.From==81 || Move.To==81) NewPosition[WROOK8MOVED]=TRUE;
	if (Move.From==18 || Move.To==18) NewPosition[BROOK1MOVED]=TRUE;
	if (Move.From==88 || Move.To==88) NewPosition[BROOK8MOVED]=TRUE;
/*************************************************************************
We need to set the [ENPAWN] file.
**************************************************************************/
	NewPosition[ENPAWN]=0;
	if (*FromPiece==WP && GetRank[Move.From]==2 && GetRank[Move.To]==4) NewPosition[ENPAWN]=GetFile[Move.To];
	if (*FromPiece==BP && GetRank[Move.From]==7 && GetRank[Move.To]==5) NewPosition[ENPAWN]=GetFile[Move.To];
// Change the side to move
#ifndef NOZORBRIST
	HashKey^=PieceSquareValues[0][1];
	HashKey^=PieceSquareValues[0][0];
#ifdef CHARPOSITION
	NewPosition[HASHKEYFIELD1]=HashKey/HASHDIV3;
	NewPosition[HASHKEYFIELD2]=HashKey%HASHDIV3/HASHDIV2;
	NewPosition[HASHKEYFIELD3]=HashKey%HASHDIV2/HASHDIV1;
	NewPosition[HASHKEYFIELD4]=HashKey%HASHDIV1;
#else
	NewPosition[HASHKEYFIELD1]=HashKey;
#endif
#endif
	AlterLocationInformation;
/*************************************************************************
Before we change the side to move, let's check to see if the move would
leave the mover in check.  If so, we must return 0.
**************************************************************************/
	if (IsCheck(NewPosition)) {
		 return 0;
	}
	if (NewPosition[MOVER]==WHITE) NewPosition[MOVER]=BLACK; else NewPosition[MOVER]=WHITE;
/*************************************************************************
Turn this on to test whether the hash value is calculated
correctly on the fly
**************************************************************************/
#ifdef HASHCHECK
	if (HashKey!=ComputeHashKey(NewPosition)) {
		FILE* f;
		f=fopen("c:\\log.txt", "a");
		fprintf( f, "Original Calculated: %i\n", ComputeHashKey(Position) );
		fprintf( f, "Final Calculated: %i\n", ComputeHashKey(NewPosition) );
		char s1[500]; char s2[500]; int p[89];
		for (int x=0; x<89; x++) p[x]=Position[x];
		TChessBoard* a = new TChessBoard(p); a->GetFEN(s1);
		delete a;
		for (x=0; x<89; x++) p[x]=NewPosition[x];
		a = new TChessBoard(p); a->GetFEN(s2);
		delete a;
		fprintf(f, "Mover: %s\n%s1\n%s2\nMove: %i-%i=%i\nOrig: %i HashKey %i\n", (Position[MOVER]==WHITE ? "White" : "Black"), s1, s2, Move.From, Move.To, Move.PromotionPiece, OrigKey, HashKey);
		fprintf(f, "[81][WR] %i [11][BN] %i [11][WR] %i\n", PieceSquareValues[81][WR-1], PieceSquareValues[11][BN-95], PieceSquareValues[11][WR-1]);
		ExitWithMove();
		fclose(f);
	}
#endif
	NewPosition[LASTMOVESQUARE]=Move.To;
	return 1;
}

int
TSearcher::MakeMoveQuick(TPosition Position, TMove& Move, TPosition NewPosition)
{
	int TypeIndex, PieceIndex;
	memcpy(NewPosition, Position, SIZEOFPOSITION);
/*************************************************************************
First we make the move.  In the rest of the function we will modify the
new position if required, (castling, promotion, en-passant, for example).
**************************************************************************/
	POSITIONELEMENT *FromPiece=Position+Move.From;
	POSITIONELEMENT *ToPiece=Position+Move.To;
	NewPosition[Move.To]=*FromPiece;
	NewPosition[Move.From]=EMPTY;
/*************************************************************************
For kings, we need to make alterations for castling moves and also we need
to update the NewPosition[xKINGPOSITION] values.  Also we flag that the
king has moved to avoid future castling.
**************************************************************************/
	if (*FromPiece==WK) {
		NewPosition[WKINGPOSITION]=Move.To;
		NewPosition[WKINGMOVED]=TRUE;
		if (Move.From==51 && Move.To==31) {
			NewPosition[41]=WR;
			NewPosition[11]=EMPTY;
		}
		if (Move.From==51 && Move.To==71) {
			NewPosition[61]=WR;
			NewPosition[81]=EMPTY;
		}
	}
	if (*FromPiece==BK) {
		NewPosition[BKINGPOSITION]=Move.To;
		NewPosition[BKINGMOVED]=TRUE;
		if (Move.From==58 && Move.To==38) {
			NewPosition[48]=BR;
			NewPosition[18]=EMPTY;
		}
		if (Move.From==58 && Move.To==78) {
			NewPosition[68]=BR;
			NewPosition[88]=EMPTY;
		}
	}
/*************************************************************************
For pawns, we need to make alterations for promotions and en-passant moves.
**************************************************************************/
	if (*FromPiece==WP) {
	  if (GetRank[Move.To]==8) {
		  NewPosition[Move.To]=Move.PromotionPiece;
	  }
	  if ((Move.From-Move.To==-11 || Move.From-Move.To==9) && *ToPiece==EMPTY) {
		  NewPosition[Move.To-1]=EMPTY;
	  }
	}
	if (*FromPiece==BP) {
	  if (GetRank[Move.To]==1) {
		  NewPosition[Move.To]=Move.PromotionPiece+100;
	  }
	  if ((Move.From-Move.To==11 || Move.From-Move.To==-9) && *ToPiece==EMPTY) {
		  NewPosition[Move.To+1]=EMPTY;
	  }
	}
/*************************************************************************
For rooks, we need to flag their movements for castling privelege purposes.
**************************************************************************/
	if (Move.From==11 || Move.To==11) NewPosition[WROOK1MOVED]=TRUE;
	if (Move.From==81 || Move.To==81) NewPosition[WROOK8MOVED]=TRUE;
	if (Move.From==18 || Move.To==18) NewPosition[BROOK1MOVED]=TRUE;
	if (Move.From==88 || Move.To==88) NewPosition[BROOK8MOVED]=TRUE;
	AlterLocationInformation;
	if (NewPosition[MOVER]==WHITE) NewPosition[MOVER]=BLACK; else NewPosition[MOVER]=WHITE;
	NewPosition[LASTMOVESQUARE]=Move.To;
	return 1;
}

int GetSquareColour(int sq)
{
	if ((GetX(sq) + GetY(sq)) % 2 == 0)
	{
		return BLACK;
	}
	else
	{
		return WHITE;
	}
}

void 
TSearcher::ShowPosition(TPosition Position)
{
	cout << "*******************************" << LOG_ENDL;
	for (int y=8; y>=1; y--)
	{
		for (int x=1; x<=8; x++)
		{
			switch (Position[x*10+y])
			{
				case WP : cout << "P"; break;
				case WQ : cout << "Q"; break;
				case WN : cout << "N"; break;
				case WR : cout << "R"; break;
				case WB : cout << "B"; break;
				case WK : cout << "K"; break;
				case BP : cout << "p"; break;
				case BQ : cout << "q"; break;
				case BN : cout << "n"; break;
				case BR : cout << "r"; break;
				case BB : cout << "b"; break;
				case BK : cout << "k"; break;
				default : cout << "-"; break;
			}
		}
		cout << LOG_ENDL;
	}
	cout << "*******************************" << LOG_ENDL;
}

int
TSearcher::KingSafety(TPosition Position)
{
/**************************************************************************
Makeshift King safety function.  Prevents Rival neglecting the king but
doesn't contain much knowledge.
Evaluates from White King Side Castle point of view, position is modified
prior to calling.
**************************************************************************/

	int Surround=(Position[62]==PAWN)+(Position[63]==PAWN)+
					 (Position[72]==PAWN)+(Position[73]==PAWN)+
					 (Position[82]==PAWN)+(Position[83]==PAWN)+
					 (Position[63]==KNIGHT)+(Position[72]==BISHOP);

	int Score=Surround*KINGSAFETYUNIT;

	int EnemySurround = 0;
	for (int x=5; x<=8; x++)
	{
		for (int y=1; y<=4; y++)
		{
			if (Position[x*10+y] > EMPTY)
			{
				EnemySurround += KINGSAFETYUNIT * 3;
			}
		}
	}

	Score -= EnemySurround;

	if (Position[62]==PAWN && Position[72]==PAWN && Position[82]==PAWN) {
		// A.  Three straight pawns.  Bonus if knight protects H-Pawn
		Score+=KINGSAFETYSTRONG;
		if (Position[63]==KNIGHT) Score+=KINGSAFETYUNIT;
	} else
	if (Position[62]==PAWN && Position[73]==PAWN && Position[82]==PAWN && Position[72]==BISHOP) {
		// B. Even stronger if opponent doesn't have same colour bishop.
		Score+=KINGSAFETYSTRONG;
	} else
	if (Position[62]==PAWN && Position[73]==PAWN && Position[83]==PAWN) {
		// C.
		Score+=KINGSAFETYQUITESTRONG;
	} else
	if (Position[62]==PAWN && Position[72]==PAWN && Position[83]==PAWN) {
		// D.  H pawn on rank 3.  Should also check the danger that the
		// opponent has the bishop that can attack the h-pawn.
		Score+=KINGSAFETYQUITESTRONG;
		if (Position[63]==KNIGHT) Score+=KINGSAFETYUNIT;
	} else
	if (Position[64]==PAWN && Position[72]==PAWN && Position[82]==PAWN) {
		// E.
		Score+=KINGSAFETYSTRONG;
		if (Position[63]==KNIGHT) Score+=KINGSAFETYUNIT;
	} else
	if (Position[63]==PAWN && Position[72]==PAWN && Position[82]==PAWN) {
		// F.
		Score+=KINGSAFETYQUITEWEAK;
	} else
	if (Position[62]==PAWN && Position[73]==PAWN && Position[82]==PAWN) {
		// G. Only score if no opposite queen
		if (Position[MOVER]==WHITE && !Position[BLACKQUEENS])	Score+=KINGSAFETYVERYWEAK; else
		if (Position[MOVER]==BLACK && !Position[WHITEQUEENS])	Score+=KINGSAFETYVERYWEAK;
	} else
	if (Position[63]==PAWN && Position[72]==PAWN && Position[83]==PAWN) {
		// H.
		Score+=KINGSAFETYVERYWEAK;
	} else
	if (Position[64]==PAWN && Position[73]==PAWN && Position[82]==PAWN) {
		// I. Award points only if knight and bishop well placed
		if (Position[63]==KNIGHT && Position[72]==BISHOP) {
			Score+=KINGSAFETYQUITEWEAK;
		}
	} 

	return Score; 
}

int
TSearcher::FastEvaluate(TPosition Position, int Lowest, int Highest)
{
#ifdef TESTING
	int t1 = GetTickCount();
#endif

	 CurrentPathNodes++;

	 TimerAndPVCode;

	 int WhiteMajorPieces=Position[WHITEROOKS]*ROOKVALUE+Position[WHITEQUEENS]*QUEENVALUE;
	 int BlackMajorPieces=Position[BLACKROOKS]*ROOKVALUE+Position[BLACKQUEENS]*QUEENVALUE;
	 int WhiteMinorPieces=Position[WHITEKNIGHTS]*KNIGHTVALUE+Position[WHITEBISHOPS]*BISHOPVALUE;
	 int BlackMinorPieces=Position[BLACKKNIGHTS]*KNIGHTVALUE+Position[BLACKBISHOPS]*BISHOPVALUE;
	 int WhitePieces=WhiteMajorPieces+WhiteMinorPieces;
	 int BlackPieces=BlackMajorPieces+BlackMinorPieces;

	 int WhiteScore=WhitePieces+Position[WHITEPAWNS]*PAWNVALUE;
	 int BlackScore=BlackPieces+Position[BLACKPAWNS]*PAWNVALUE;

	 int OpeningPhase;
	 int EndgamePhase=FALSE;

 	 if (Position[MOVER]==WHITE) {
		OpeningPhase=
		(!Position[WHITECASTLED] && !Position[WKINGMOVED] && !(Position[WROOK1MOVED] && Position[WROOK8MOVED])) ||
			(WhitePieces >= OPENINGPIECES && (Position[21]==WN || Position[31]==WB || Position[61]==WB || Position[71]==WN));
	 } else {
		OpeningPhase=
		(!Position[BLACKCASTLED] && !Position[BKINGMOVED] && !(Position[BROOK1MOVED] && Position[BROOK8MOVED])) ||
			(BlackPieces >= OPENINGPIECES && (Position[28]==BN || Position[38]==BB || Position[68]==BB || Position[78]==BN));
	 }
	 if (!OpeningPhase) 
	 {
		EndgamePhase=(WhitePieces<=ENDGAMEPIECES && BlackPieces<=ENDGAMEPIECES);
	 }

		 for (i=11; i<=88; i++)
		 {
			 switch (Position[i])
			 {
				case WP : WhiteScore += WhitePawnPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case WQ : WhiteScore += WhiteQueenPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case WN : WhiteScore += WhiteKnightPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case WB : WhiteScore += WhiteBishopPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case WK : WhiteScore += WhiteKingPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case WR : WhiteScore += WhiteRookPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case BP : BlackScore += BlackPawnPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case BQ : BlackScore += BlackQueenPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case BN : BlackScore += BlackKnightPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case BB : BlackScore += BlackBishopPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case BK : BlackScore += BlackKingPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case BR : BlackScore += BlackRookPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
			 }
		 }
#ifdef TESTING
	int t2 = GetTickCount() - t1;
	TotalEvaluateCalls++;
	TotalEvaluateMillis += t2;
#endif

	 if (Position[MOVER]==WHITE) 
	 {
		return (int)((WhiteScore-BlackScore)*0.1);
	 } 
	 else 
	 {
		return (int)((BlackScore-WhiteScore)*0.1);
	 }

}

int 
TSearcher::Evaluate()
{
	return Evaluate(StartPosition, LOWEVAL, HIGHEVAL);
}

int 
TSearcher::Evaluate(TPosition Position, int Lowest, int Highest)
{
	//return FastEvaluate(Position, Lowest, Highest);
#ifdef TESTING
	int t1 = GetTickCount();
#endif
	 CurrentPathNodes++;

	 TimerAndPVCode;

	 int i;
	 int OpeningPhase;
	 int EndgamePhase=FALSE;

/**************************************************************************
Populate some variables for use later on.
**************************************************************************/
	 int WhiteMajorPieces=Position[WHITEROOKS]*ROOKVALUE+Position[WHITEQUEENS]*QUEENVALUE;
	 int BlackMajorPieces=Position[BLACKROOKS]*ROOKVALUE+Position[BLACKQUEENS]*QUEENVALUE;
	 int WhiteMinorPieces=Position[WHITEKNIGHTS]*KNIGHTVALUE+Position[WHITEBISHOPS]*BISHOPVALUE;
	 int BlackMinorPieces=Position[BLACKKNIGHTS]*KNIGHTVALUE+Position[BLACKBISHOPS]*BISHOPVALUE;
	 int WhitePieces=WhiteMajorPieces+WhiteMinorPieces;
	 int BlackPieces=BlackMajorPieces+BlackMinorPieces;

/**************************************************************************
If one side has a lone king, evaluate for mate.
**************************************************************************/
	 if ((WhitePieces==0 || BlackPieces==0) && Position[WHITEPAWNS]==0 && Position[BLACKPAWNS]==0)
	 {
		 return LoneKing(Position);
	 }

	 int WhiteScore=WhitePieces+Position[WHITEPAWNS]*PAWNVALUE;
	 int BlackScore=BlackPieces+Position[BLACKPAWNS]*PAWNVALUE;

/**************************************************************************
Bonus for the bishop pair
**************************************************************************/
	 WhiteScore += (Position[WHITEBISHOPS] == 2 ? BISHOPPAIRBONUS : 0);
	 BlackScore += (Position[BLACKBISHOPS] == 2 ? BISHOPPAIRBONUS : 0);

	 int WhiteKing=Position[WKINGPOSITION];
	 int BlackKing=Position[BKINGPOSITION];
	 int PawnRank, PawnFileIndex, PotentialPawnRank;
	 POSITIONELEMENT* v=Position+WHITEPAWNS;
/**************************************************************************
Is this the opening, middlegame or the endgame?
**************************************************************************/
 	 if (Position[MOVER]==WHITE) {
		OpeningPhase=
		(!Position[WHITECASTLED] && !Position[WKINGMOVED] && !(Position[WROOK1MOVED] && Position[WROOK8MOVED])) ||
			(WhitePieces >= OPENINGPIECES && (Position[21]==WN || Position[31]==WB || Position[61]==WB || Position[71]==WN));
	 } else {
		OpeningPhase=
		(!Position[BLACKCASTLED] && !Position[BKINGMOVED] && !(Position[BROOK1MOVED] && Position[BROOK8MOVED])) ||
			(BlackPieces >= OPENINGPIECES && (Position[28]==BN || Position[38]==BB || Position[68]==BB || Position[78]==BN));
	 }

	 if (!OpeningPhase) 
	 {
		EndgamePhase=(WhitePieces<=ENDGAMEPIECES && BlackPieces<=ENDGAMEPIECES);

		if (EndgamePhase)
		{
/**************************************************************************
If bishop vs bishop and opposing bishops are opposite colours, penalise the side with the most pawns
**************************************************************************/
			if (Position[WHITEBISHOPS] == 1 && Position[BLACKBISHOPS] == 1 && WhitePieces==BISHOPVALUE && BlackPieces==BISHOPVALUE)
			{
				if (GetSquareColour(Position[WHITEBISHOPS+1]) != GetSquareColour(Position[BLACKBISHOPS+1]))
				{
					if (Position[WHITEPAWNS] > Position[BLACKPAWNS])
					{
						WhiteScore -= 700;
					}
					if (Position[BLACKPAWNS] > Position[WHITEPAWNS])
					{
						BlackScore -= 700;
					}
				}
			}
		}
	 } else {
/**************************************************************************
Evaluate piece development in the opening.
**************************************************************************/
		int WhiteUnmovedMinors=((Position[21]==WN)+(Position[31]==WB)+(Position[61]==WB)+(Position[71]==WN));
		int BlackUnmovedMinors=((Position[28]==BN)+(Position[38]==BB)+(Position[68]==BB)+(Position[78]==BN));
		WhiteScore-=WhiteUnmovedMinors*UNDEVELOPEDMINOR;
		BlackScore-=BlackUnmovedMinors*UNDEVELOPEDMINOR;
		if (WhiteUnmovedMinors==4 && Position[41]!=WQ) WhiteScore-=QUEENOUTEARLY;
		if (BlackUnmovedMinors==4 && Position[48]!=BQ) BlackScore-=QUEENOUTEARLY;
		WhiteScore+=CENTRALOCCUPATION*((Position[44]<EMPTY) + (Position[45]<EMPTY) + (Position[54]<EMPTY) + (Position[55]<EMPTY));
		BlackScore+=CENTRALOCCUPATION*((Position[44]>EMPTY) + (Position[45]>EMPTY) + (Position[54]>EMPTY) + (Position[55]>EMPTY));
	 }

#ifdef USEPIECESQUARETABLESINEVAL
	 if (!EndgamePhase)
	 {
		 for (i=11; i<=88; i++)
		 {
			 switch (Position[i])
			 {
				case WP : WhiteScore += WhitePawnPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case WQ : WhiteScore += WhiteQueenPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case WN : WhiteScore += WhiteKnightPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case WB : WhiteScore += WhiteBishopPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case WK : WhiteScore += WhiteKingPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case WR : WhiteScore += WhiteRookPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case BP : BlackScore += BlackPawnPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case BQ : BlackScore += BlackQueenPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case BN : BlackScore += BlackKnightPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case BB : BlackScore += BlackBishopPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case BK : BlackScore += BlackKingPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
				case BR : BlackScore += BlackRookPieceSquareTable[i] * PIECESQUAREEVALMULTIPLIER; break;
			 }
		 }
	 }
#endif
/**************************************************************************
Evaluate each piece in turn.
First Pawns which get a bonus for advancing.
**************************************************************************/
	 int MostAdvancedWhitePawn[9]={0, 0, 0, 0, 0, 0, 0, 0, 0};
	 int LeastAdvancedWhitePawn[9]={9, 9, 9, 9, 9, 9, 9, 9, 9};
	 for (v+=*v; v!=Position+WHITEPAWNS; v--) 
	 {
		WhiteScore+=(EndgamePhase ? WhitePawnAdvance[*v] : 0);
		PawnRank=GetRank[*v];
		PawnFileIndex=GetFile[*v];
		if (PawnRank>MostAdvancedWhitePawn[PawnFileIndex]) MostAdvancedWhitePawn[PawnFileIndex]=PawnRank;
		if (PawnRank<LeastAdvancedWhitePawn[PawnFileIndex]) LeastAdvancedWhitePawn[PawnFileIndex]=PawnRank;
	 }
	 int MostAdvancedBlackPawn[9]={9, 9, 9, 9, 9, 9, 9, 9, 9};
	 int LeastAdvancedBlackPawn[9]={0, 0, 0, 0, 0, 0, 0, 0, 0};
	 for (v+=(BLACKPAWNS-WHITEPAWNS), v+=*v; v!=Position+BLACKPAWNS; v--) 
	 {
		BlackScore+=(EndgamePhase ? BlackPawnAdvance[*v] : 0);
		PawnRank=GetRank[*v];
		PawnFileIndex=GetFile[*v];
		if (PawnRank<MostAdvancedBlackPawn[PawnFileIndex]) MostAdvancedBlackPawn[PawnFileIndex]=PawnRank;
		if (PawnRank>LeastAdvancedBlackPawn[PawnFileIndex]) LeastAdvancedBlackPawn[PawnFileIndex]=PawnRank;
	 }
//goto PositionalEvalSkip;
/**************************************************************************
Evaluate Rooks for Mobility, King Tropism (take distance from score),
Seventh Rank, Open/Semi-Open Files and Doubled on same Rank or File.
**************************************************************************/
	 for (v+=(WHITEROOKS-BLACKPAWNS), v+=*v; v!=Position+WHITEROOKS; v--) {
		for (i=*v+10; i<90; i+=10) if (Position[i]==EMPTY) WhiteScore+=ROOKRANKMOBILITY; else {if (Position[i]==WR) WhiteScore+=DOUBLEDFILEROOKS; break;}
		for (i=*v-10; i>9; i-=10) if (Position[i]==EMPTY) WhiteScore+=ROOKRANKMOBILITY;	else {if (Position[i]==WR) WhiteScore+=DOUBLEDFILEROOKS; break;}
		for (i=*v-1; Valid[i]; i--) if (Position[i]==EMPTY) WhiteScore+=ROOKFILEMOBILITY; else {if (Position[i]==WR) WhiteScore+=DOUBLEDRANKROOKS; break;}
		for (i=*v+1; Valid[i]; i++) if (Position[i]==EMPTY) WhiteScore+=ROOKFILEMOBILITY; else {if (Position[i]==WR) WhiteScore+=DOUBLEDRANKROOKS; break;}
		WhiteScore+=(-RookKingTropism[*v][BlackKing])+(WhiteSeventhRank[*v] ? ROOKSEVENTHRANK : 0)+
		(MostAdvancedWhitePawn[GetFile[*v]]==0 ? MostAdvancedBlackPawn[GetFile[*v]]==9 ? ROOKONOPENFILE : ROOKONSEMIOPENFILE : 0);
	 }
	 for (v+=(BLACKROOKS-WHITEROOKS), v+=*v; v!=Position+BLACKROOKS; v--) {
		for (i=*v+10; i<90; i+=10) if (Position[i]==EMPTY) BlackScore+=ROOKRANKMOBILITY; else {if (Position[i]==BR) BlackScore+=DOUBLEDFILEROOKS; break;}
		for (i=*v-10; i>9; i-=10) if (Position[i]==EMPTY) BlackScore+=ROOKRANKMOBILITY;	else {if (Position[i]==BR) BlackScore+=DOUBLEDFILEROOKS; break;}
		for (i=*v-1; Valid[i]; i--) if (Position[i]==EMPTY) BlackScore+=ROOKFILEMOBILITY; else {if (Position[i]==BR) BlackScore+=DOUBLEDRANKROOKS; break;}
		for (i=*v+1; Valid[i]; i++) if (Position[i]==EMPTY) BlackScore+=ROOKFILEMOBILITY; else {if (Position[i]==BR) BlackScore+=DOUBLEDRANKROOKS; break;}
		BlackScore+=(-RookKingTropism[*v][WhiteKing])+(BlackSeventhRank[*v] ? ROOKSEVENTHRANK : 0)+
		(MostAdvancedBlackPawn[GetFile[*v]]==9 ? MostAdvancedWhitePawn[GetFile[*v]]==0 ? ROOKONOPENFILE : ROOKONSEMIOPENFILE : 0);
	 }
/**************************************************************************
Evaluate Knights for piece square bonus and King Tropism (added this time)
**************************************************************************/
	 for (v+=(WHITEKNIGHTS-BLACKROOKS), v+=*v; v!=Position+WHITEKNIGHTS; WhiteScore+=(knightcontrol[*v]+KnightKingTropism[*v][BlackKing]), v--);
	 for (v+=(BLACKKNIGHTS-WHITEKNIGHTS), v+=*v; v!=Position+BLACKKNIGHTS; BlackScore+=(knightcontrol[*v]+KnightKingTropism[*v][WhiteKing]), v--);
/**************************************************************************
Evaluate Bishops for Mobility and King Tropism (take distance from score)
**************************************************************************/
	 for (v+=(WHITEBISHOPS-BLACKKNIGHTS), v+=*v; v!=Position+WHITEBISHOPS; v--) {
		WhiteScore+=(knightcontrol[*v]-BishopKingTropism[*v][BlackKing]);
		for (i=*v+11; Valid[i]; i+=11) if (Position[i]==EMPTY) WhiteScore+=BISHOPMOBILITY; else break;
		for (i=*v+9; Valid[i]; i+=9) if (Position[i]==EMPTY) WhiteScore+=BISHOPMOBILITY; else break;
		for (i=*v-11; Valid[i]; i-=11) if (Position[i]==EMPTY) WhiteScore+=BISHOPMOBILITY; else break;
		for (i=*v-9; Valid[i]; i-=9) if (Position[i]==EMPTY) WhiteScore+=BISHOPMOBILITY; else break;
	 }
	 for (v+=(BLACKBISHOPS-WHITEBISHOPS), v+=*v; v!=Position+BLACKBISHOPS; v--) {
		BlackScore+=(knightcontrol[*v]-BishopKingTropism[*v][WhiteKing]);
		for (i=*v+11; Valid[i]; i+=11) if (Position[i]==EMPTY) BlackScore+=BISHOPMOBILITY; else break;
		for (i=*v+9; Valid[i]; i+=9) if (Position[i]==EMPTY) BlackScore+=BISHOPMOBILITY; else break;
		for (i=*v-11; Valid[i]; i-=11) if (Position[i]==EMPTY) BlackScore+=BISHOPMOBILITY; else break;
		for (i=*v-9; Valid[i]; i-=9) if (Position[i]==EMPTY) BlackScore+=BISHOPMOBILITY; else break;
	 }
/**************************************************************************
Evaluate Queens for Mobility and King Tropism (take distance from score)
**************************************************************************/
	 for (v+=(WHITEQUEENS-BLACKBISHOPS), v+=*v; v!=Position+WHITEQUEENS; v--) WhiteScore-=QueenKingTropism[*v][BlackKing];
	 for (v+=(BLACKQUEENS-WHITEQUEENS), v+=*v; v!=Position+BLACKQUEENS; v--) BlackScore-=QueenKingTropism[*v][WhiteKing];

/**************************************************************************
King safety.
Award points for safe king positions.
Before calling the king safety method, the bottom right side of the board
is populated with the castled position of the side to evaluate.  That is,
if black has castled queen side, the pieces around the black king are
transposed to the bottom right hand side of the board as if it were a
white king side castle.  This slows the routine slightly but ensures that
the position is evaluated the same for all four castle positions.
**************************************************************************/
	 int WhiteKingSafety=0;
	 int BlackKingSafety=0;

#ifdef NEWKINGSAFETY
	if (!EndgamePhase) 
	{
		int KingFile = GetFile[WhiteKing];
		int KingRank = GetRank[WhiteKing];
		int StartFile = (KingFile > 1 ? KingFile - 1 : KingFile);
		int EndFile = (KingFile < 8 ? KingFile + 1 : KingFile);
		int j;
		int Lap;

		for (i=StartFile; i<=EndFile; i++)
		{
			Lap = LeastAdvancedWhitePawn[i];
			if (Lap == 9)
			{
				WhiteKingSafety -= KINGSAFETY_PAWNMISSING;
			}

			// For each square beneath the pawn on this file down to rank 3 (the last rank that can be defended by a pawn),
			// penalise if the least advanced pawns on the adjacent ranks are both equal to or higher ranks than this one (no defence left for this file)
			for (j=4; j>2; j--)
			{
				if ((i==1 || LeastAdvancedWhitePawn[i-1] >= j) && (i==8 || LeastAdvancedWhitePawn[i+1] >= j))
				{
					WhiteKingSafety -= KINGSAFETY_HOLEINDEFENCE;
				}
			}
		}

		if (KingFile == 4 || KingFile == 5)
		{
			WhiteKingSafety -= KINGSAFETY_NOTYETCASTLED;
		}

		if (KingRank != 1)
		{
			WhiteKingSafety -= KINGSAFETY_NOTONBACKRANK;
		}

		 if (!Position[WHITECASTLED]) 
		 {
			if (Position[WKINGMOVED]) 
			{
				WhiteKingSafety-=NOCASTLEPOSSIBLE; 
			}
			else 
			{
				if (Position[WROOK8MOVED]) 
				{
					WhiteKingSafety-=KINGCASTLENOPOSSIBLE;
				}
				if (Position[WROOK1MOVED])	
				{
					WhiteKingSafety-=QUEENCASTLENOPOSSIBLE;
				}
			}
		 }

		KingFile = GetFile[BlackKing];
		KingRank = GetRank[BlackKing];
		StartFile = (KingFile > 1 ? KingFile - 1 : KingFile);
		EndFile = (KingFile < 8 ? KingFile + 1 : KingFile);

		for (i=StartFile; i<=EndFile; i++)
		{
			Lap = LeastAdvancedBlackPawn[i];
			if (Lap == 0)
			{
				BlackKingSafety -= KINGSAFETY_PAWNMISSING;
			}

			for (j=5; j<7; j++)
			{
				if ((i==1 || LeastAdvancedBlackPawn[i-1] <= j) && (i==8 || LeastAdvancedBlackPawn[i+1] <= j))
				{
					BlackKingSafety -= KINGSAFETY_HOLEINDEFENCE;
				}
			}
		}

		if (KingFile == 4 || KingFile == 5)
		{
			BlackKingSafety -= KINGSAFETY_NOTYETCASTLED;
		}

		if (KingRank != 8)
		{
			BlackKingSafety -= KINGSAFETY_NOTONBACKRANK;
		}

		if (!Position[BLACKCASTLED]) 
		{
			if (Position[BKINGMOVED]) 
			{
				BlackKingSafety-=NOCASTLEPOSSIBLE; 
			}
			else 
			{
				if (Position[BROOK8MOVED]) 
				{
					BlackKingSafety-=KINGCASTLENOPOSSIBLE;
				}
				if (Position[BROOK1MOVED])	
				{
					BlackKingSafety-=QUEENCASTLENOPOSSIBLE;
				}
			}
		}

#ifdef TESTING
		//ShowPosition(Position);
#endif
		int MultiSubtract = ROOKVALUE * 2;
		int Multiplier = Position[BLACKKNIGHTS] + Position[BLACKBISHOPS] + Position[BLACKQUEENS] + Position[BLACKROOKS];
		WhiteKingSafety = WhiteKingSafety * Multiplier;
		Multiplier = Position[WHITEKNIGHTS] + Position[WHITEBISHOPS] + Position[WHITEQUEENS] + Position[WHITEROOKS];
		BlackKingSafety = BlackKingSafety * Multiplier;
#ifdef TESTING
		//cout << "White King Safety = " << WhiteKingSafety << LOG_ENDL;
		//cout << "Black King Safety = " << BlackKingSafety << LOG_ENDL;
#endif
		WhiteScore += WhiteKingSafety;
		BlackScore += BlackKingSafety;

	 }
#else
	 if (!EndgamePhase) {
		 int x, y;
		 TPosition NewPosition;
		 NewPosition[MOVER]=Position[MOVER];
		 NewPosition[WHITEQUEENS]=Position[WHITEQUEENS];
		 NewPosition[BLACKQUEENS]=Position[BLACKQUEENS];
		 if (GetRank[WhiteKing]<3 && (GetFile[WhiteKing]<4 || GetFile[WhiteKing]>5)) {
			 if (WhiteKing==11 || WhiteKing==21 || WhiteKing==31) {
				for (x=5; x<=8; x++)
					for (y=1; y<=4; y++) {
						NewPosition[x*10+y]=Position[(9-x)*10+y];
						if (NewPosition[x*10+y]>EMPTY) WhiteKingSafety-=KINGSAFETYUNIT;
						if (NewPosition[x*10+y]==BQ) WhiteKingSafety-=KINGSAFETYUNIT;
					}
			 } else {
				for (x=5; x<=8; x++)
					for (y=1; y<=4; y++) {
						NewPosition[x*10+y]=Position[x*10+y];
						if (NewPosition[x*10+y]>EMPTY) WhiteKingSafety-=KINGSAFETYUNIT;
						if (NewPosition[x*10+y]==BQ) WhiteKingSafety-=KINGSAFETYUNIT;
					}
			 }
			 //ShowPosition(Position);
			 //ShowPosition(NewPosition);
			 WhiteKingSafety+=KingSafety(NewPosition);
			 WhiteScore+=WhiteKingSafety;
		 }
		 if (GetRank[BlackKing]>6 && (GetFile[BlackKing]<4 || GetFile[BlackKing]>5)) {
			 if (BlackKing==18 || BlackKing==28 || BlackKing==38) {
				for (x=5; x<=8; x++)
					for (y=1; y<=4; y++) {
						NewPosition[x*10+y]=Position[(9-x)*10+(9-y)];
						if (NewPosition[x*10+y]<EMPTY) NewPosition[x*10+y]+=100; else
						if (NewPosition[x*10+y]>EMPTY) NewPosition[x*10+y]-=100;
						if (NewPosition[x*10+y]>EMPTY) BlackKingSafety-=KINGSAFETYUNIT;
						if (NewPosition[x*10+y]==BQ) BlackKingSafety-=KINGSAFETYUNIT;
					}
			 } else {
				for (x=5; x<=8; x++)
					for (y=1; y<=4; y++) {
						NewPosition[x*10+y]=Position[x*10+(9-y)];
						if (NewPosition[x*10+y]<EMPTY) NewPosition[x*10+y]+=100; else
						if (NewPosition[x*10+y]>EMPTY) NewPosition[x*10+y]-=100;
						if (NewPosition[x*10+y]>EMPTY) BlackKingSafety-=KINGSAFETYUNIT;
						if (NewPosition[x*10+y]==BQ) BlackKingSafety-=KINGSAFETYUNIT;
					}
			 }
			 BlackKingSafety+=KingSafety(NewPosition);
			 BlackScore+=BlackKingSafety;
		 }
	 }
#endif
/**************************************************************************
Evaluate Pawn Structure.  Penalise doubled/isolated pawns a fixed value.
Award a fixed bonus for passed pawns.
**************************************************************************/
	 // for each pawn file
	 for (i=9; --i; ) 
	 {
		/* any pawns on this file? */
		if (MostAdvancedWhitePawn[i]>0) {
			/* Most advanced friendly pawn */
			PawnRank=MostAdvancedWhitePawn[i];
			/* more than one? */
			if (LeastAdvancedWhitePawn[i]!=PawnRank) 
			{
				WhiteScore-=DOUBLEDPAWNS;
			}
			/* no friendly pawn on left or right of this file? */
			if ((i==1 || MostAdvancedWhitePawn[i-1]==0) && (i==8 || MostAdvancedWhitePawn[i+1]==0)) WhiteScore-=ISOLATEDPAWN;
			PotentialPawnRank=PawnRank;
			if (Position[MOVER]==WHITE) 
			{
				if (Position[i*10+(PawnRank+1)]==EMPTY)
				{
					PotentialPawnRank++;
				}
			}
			/* no opposition pawn blocking on left or right of this file? */
			if (LeastAdvancedBlackPawn[i]<=PotentialPawnRank && (i==1 || LeastAdvancedBlackPawn[i-1]<=PotentialPawnRank) && (i==8 || LeastAdvancedBlackPawn[i+1]<=PotentialPawnRank)) 
			{
				WhiteScore+=PASSEDPAWN*PawnRank;
				if (BlackPieces==0) 
				{
					// Opponent's king too far behind
					if (PawnRank-GetRank[BlackKing] > 1) 
					{
						WhiteScore+=(PASSEDPAWNHOME*PawnRank); 
					}
					else
					// Opponent king can't get into the magic square!
					if (abs(GetFile[BlackKing]-i)>(9-PotentialPawnRank)) 
					{
						WhiteScore+=(PASSEDPAWNHOME*PawnRank);
					}
				}
			}
			/* Backward Pawn?  Semi-open file (no enemy pawn) and behind pawns on adjacent files. */
			if (MostAdvancedBlackPawn[i] == 9)
			{
				if ((i==1 || LeastAdvancedWhitePawn[i-1]>PawnRank) && (i==8 || LeastAdvancedWhitePawn[i+1]>PawnRank))
				{
					WhiteScore -= BACKWARDPAWNPENALTY;
				}
			}
		}
		if (MostAdvancedBlackPawn[i]<9) 
		{
			PawnRank=MostAdvancedBlackPawn[i];
			if (LeastAdvancedBlackPawn[i]!=PawnRank) 
			{
				BlackScore-=DOUBLEDPAWNS;
			}
			if ((i==1 || MostAdvancedBlackPawn[i-1]==9) && (i==8 || MostAdvancedBlackPawn[i+1]==9)) BlackScore-=ISOLATEDPAWN;
			PotentialPawnRank=PawnRank;
			if (Position[MOVER]==BLACK) 
			{
				if (Position[i*10+(PawnRank-1)]==EMPTY)
				{
					PotentialPawnRank--;
				}
			}
			if (LeastAdvancedWhitePawn[i]>=PotentialPawnRank && (i==1 || LeastAdvancedWhitePawn[i-1]>=PotentialPawnRank) && (i==8 || LeastAdvancedWhitePawn[i+1]>=PotentialPawnRank)) {
				BlackScore+=PASSEDPAWN*(9-PawnRank);
				if (WhitePieces==0) {
					if (GetRank[WhiteKing]-PotentialPawnRank > 1) 
					{
						BlackScore+=(PASSEDPAWNHOME*(9-PawnRank)); 
					}
					else
					if (abs(GetFile[WhiteKing]-i)>PotentialPawnRank) 
					{
						BlackScore+=(PASSEDPAWNHOME*(9-PawnRank));
					}
				}
			}
			/* Backward Pawn?  Semi-open file (no enemy pawn) and pawns on adjacent files are ahead. */
			if (MostAdvancedWhitePawn[i] == 0)
			{
				if ((i==1 || LeastAdvancedBlackPawn[i-1]<PawnRank) && (i==8 || LeastAdvancedBlackPawn[i+1]<PawnRank))
				{
					BlackScore -= BACKWARDPAWNPENALTY;
				}
			}
		}
	 }
/**************************************************************************
If this is the endgame then encourage the king towards the centre.  Also
give a bonus for closeness to enemy king for the side with the largest
number of pieces.  Award points for having the opposition when there are
only pawns.
**************************************************************************/
	 if (EndgamePhase) 
	 {
			WhiteScore+=(KINGCENTRE*CentreKing[WhiteKing]);
			BlackScore+=(KINGCENTRE*CentreKing[BlackKing]);
			if (WhitePieces>BlackPieces) WhiteScore+=TropismNear[WhiteKing][BlackKing]*MOVEKINGNEAR;
			if (BlackPieces>WhitePieces) BlackScore+=TropismNear[WhiteKing][BlackKing]*MOVEKINGNEAR;
			if (WhitePieces==0 && BlackPieces==0) {
				int WFile=GetFile[WhiteKing];
				int BFile=GetFile[BlackKing];
				int WRank=GetRank[WhiteKing];
				int BRank=GetRank[BlackKing];
				int Distance=0;
				if (WFile==BFile) Distance=abs(WRank-BRank); else
				if (WRank==BRank) Distance=abs(WFile-BFile); else
				if (abs(WRank-BRank)==abs(WFile-BFile)) Distance=abs(WRank-BRank);
				if (Distance==2) if (Position[MOVER]==BLACK) WhiteScore+=OPPOSITION2; else BlackScore+=OPPOSITION2;
				if (Distance==3) if (Position[MOVER]==WHITE) WhiteScore+=OPPOSITION2; else BlackScore+=OPPOSITION2;
				if (Distance==4) if (Position[MOVER]==BLACK) WhiteScore+=OPPOSITION4; else BlackScore+=OPPOSITION4;
				if (Distance==5) if (Position[MOVER]==WHITE) WhiteScore+=OPPOSITION4; else BlackScore+=OPPOSITION4;
				if (Distance==6) if (Position[MOVER]==BLACK) WhiteScore+=OPPOSITION6; else BlackScore+=OPPOSITION6;
				if (Distance==7) if (Position[MOVER]==WHITE) WhiteScore+=OPPOSITION6; else BlackScore+=OPPOSITION6;
			}
	 }


#ifdef TESTING
	int t2 = GetTickCount() - t1;
	TotalEvaluateCalls++;
	TotalEvaluateMillis += t2;
#endif

	 if (Position[MOVER]==WHITE) {
		return (int)((WhiteScore-BlackScore)*0.1);
	 } else {
		return (int)((BlackScore-WhiteScore)*0.1);
	 }
}

int 
TSearcher::IsCheck(TPosition Position)
{
#ifdef TESTING
	int t1 = GetTickCount();
#endif
	int i;
	POSITIONELEMENT* KingPointer;
	int KingSquare;
	int KingX, KingY;
	if (Position[MOVER]==WHITE)
	{
		KingSquare=Position[WKINGPOSITION];
		KingPointer=Position+KingSquare;
		  KingX=GetFile[KingSquare];
		  KingY=GetRank[KingSquare];

/* Attacking Black Knight? */
		if (Position[BLACKKNIGHTS]) {
		  if (KingX>2 && KingY>1 && *(KingPointer-21)==BN) goto InCheck;
		  if (KingX>2 && KingY<8 && *(KingPointer-19)==BN) goto InCheck;
		  if (KingX>1 && KingY>2 && *(KingPointer-12)==BN) goto InCheck;
		  if (KingX>1 && KingY<7 && *(KingPointer-8)==BN) goto InCheck;
		  if (KingX<7 && KingY<8 && *(KingPointer+21)==BN) goto InCheck;
		  if (KingX<7 && KingY>1 && *(KingPointer+19)==BN) goto InCheck;
		  if (KingX<8 && KingY<7 && *(KingPointer+12)==BN) goto InCheck;
		  if (KingX<8 && KingY>2 && *(KingPointer+8)==BN) goto InCheck;
		}
/* Attacking Black Pawn? */
		if (KingX>1 && KingY<8 && *(KingPointer-9)==BP) goto InCheck;
		if (KingX<8 && KingY<8 && *(KingPointer+11)==BP) goto InCheck;
/* Attacking Black Rook or Queen? */
		if (Position[BLACKROOKS] || Position[BLACKQUEENS]) {
		 for (i=KingSquare+1; Valid[i]; i++) if (Position[i]!=EMPTY) if (Position[i]==BQ || Position[i]==BR) goto InCheck; else break;
		 for (i=KingSquare-1; Valid[i]; i--) if (Position[i]!=EMPTY) if (Position[i]==BQ || Position[i]==BR) goto InCheck; else break;
		 for (i=KingSquare+10; i<90; i+=10) if (Position[i]!=EMPTY) if (Position[i]==BQ || Position[i]==BR) goto InCheck; else break;
		 for (i=KingSquare-10; i>9; i-=10) if (Position[i]!=EMPTY) if (Position[i]==BQ || Position[i]==BR) goto InCheck; else break;
		}
/* Attacking Black Bishop or Queen? */
		if (Position[BLACKBISHOPS] || Position[BLACKQUEENS]) {
		 for (i=KingSquare+11; Valid[i]; i+=11) if (Position[i]!=EMPTY) if (Position[i]==BQ || Position[i]==BB) goto InCheck; else break;
		 for (i=KingSquare-11; Valid[i]; i-=11) if (Position[i]!=EMPTY) if (Position[i]==BQ || Position[i]==BB) goto InCheck; else break;
		 for (i=KingSquare+9; Valid[i]; i+=9) if (Position[i]!=EMPTY) if (Position[i]==BQ || Position[i]==BB) goto InCheck; else break;
		 for (i=KingSquare-9; Valid[i]; i-=9) if (Position[i]!=EMPTY) if (Position[i]==BQ || Position[i]==BB) goto InCheck; else break;
		}
/* Attacking Black King */
		i=KingSquare-Position[BKINGPOSITION];
		if (i==-11 || i==-9 || i==+9 || i==+11 || i==-10 || i==-1 || i==+10 || i==+1)
		  goto InCheck;
	}
	if (Position[MOVER]==BLACK)
	{
		KingSquare=Position[BKINGPOSITION];
		KingPointer=Position+KingSquare;
		KingX=GetFile[KingSquare];
		KingY=GetRank[KingSquare];

/* Attacking White Knight? */
		if (Position[WHITEKNIGHTS]) {
		  if (KingX>2 && KingY>1 && *(KingPointer-21)==WN) goto InCheck;
		  if (KingX>2 && KingY<8 && *(KingPointer-19)==WN) goto InCheck;
		  if (KingX>1 && KingY>2 && *(KingPointer-12)==WN) goto InCheck;
		  if (KingX>1 && KingY<7 && *(KingPointer-8)==WN) goto InCheck;
		  if (KingX<7 && KingY<8 && *(KingPointer+21)==WN) goto InCheck;
		  if (KingX<7 && KingY>1 && *(KingPointer+19)==WN) goto InCheck;
		  if (KingX<8 && KingY<7 && *(KingPointer+12)==WN) goto InCheck;
		  if (KingX<8 && KingY>2 && *(KingPointer+8)==WN) goto InCheck;
		}
/* Attacking White Pawn? */
		if (KingX<8 && KingY>1 && *(KingPointer+9)==WP) goto InCheck;
		if (KingX>1 && KingY>1 &&  *(KingPointer-11)==WP) goto InCheck;
/* Attacking White Rook or Queen? */
		if (Position[WHITEROOKS] || Position[WHITEQUEENS]) {
		 for (i=KingSquare+1; Valid[i]; i++) if (Position[i]!=EMPTY) if (Position[i]==WQ || Position[i]==WR) goto InCheck; else break;
		 for (i=KingSquare-1; Valid[i]; i--) if (Position[i]!=EMPTY) if (Position[i]==WQ || Position[i]==WR) goto InCheck; else break;
		 for (i=KingSquare+10; i<90; i+=10) if (Position[i]!=EMPTY) if (Position[i]==WQ || Position[i]==WR) goto InCheck; else break;
		 for (i=KingSquare-10; i>9; i-=10) if (Position[i]!=EMPTY) if (Position[i]==WQ || Position[i]==WR) goto InCheck; else break;
		}
/* Attacking White Bishop or Queen? */
		if (Position[WHITEBISHOPS] || Position[WHITEQUEENS]) {
		 for (i=KingSquare+11; Valid[i]; i+=11) if (Position[i]!=EMPTY) if (Position[i]==WQ || Position[i]==WB) goto InCheck; else break;
		 for (i=KingSquare-11; Valid[i]; i-=11) if (Position[i]!=EMPTY) if (Position[i]==WQ || Position[i]==WB) goto InCheck; else break;
		 for (i=KingSquare+9; Valid[i]; i+=9) if (Position[i]!=EMPTY) if (Position[i]==WQ || Position[i]==WB) goto InCheck; else break;
		 for (i=KingSquare-9; Valid[i]; i-=9) if (Position[i]!=EMPTY) if (Position[i]==WQ || Position[i]==WB) goto InCheck; else break;
		}
/* Attacking White King */
		i=KingSquare-Position[WKINGPOSITION];
		if (i==-11 || i==-9 || i==+9 || i==+11 || i==-10 || i==-1 || i==+10 || i==+1)
		  goto InCheck;
	}
#ifdef TESTING
	int t2 = GetTickCount() - t1;
	TotalIsCheckCalls++;
	TotalIsCheckMillis += t2;
#endif
	return FALSE;
InCheck:
	return TRUE;
}

int
TSearcher::WinnerWhenNoMoves(TPosition Position)
{
	return (IsCheck(Position) ? -1 : 0);
}

int
TSearcher::PreviousPosition(TMove Move)
{
	if (CurrentDepth==0) {
	  for (int i=0; DrawMoves[i].From!=0; i++)
		  if (Move.From==DrawMoves[i].From && Move.To==DrawMoves[i].To)
			  return TRUE;
	  return FALSE;
	}
	if (CurrentDepth==1) {
	  for (int i=0; Ply1DrawMovesPly0[i].From!=0; i++)
		  if (CurrentDepthZeroMove.From==Ply1DrawMovesPly0[i].From &&
				CurrentDepthZeroMove.To==Ply1DrawMovesPly0[i].To &&
				Move.From==Ply1DrawMovesPly1[i].From &&
				Move.To==Ply1DrawMovesPly1[i].To)
				  return TRUE;
	  return FALSE;
	}
	exit(0);
}

void
TSearcher::SetupTropism()
{
	int i, j;
	for (i=0; i<89; i++) {
		GetFile[i]=i/10;
		GetRank[i]=i%10;
		for (j=0; j<89; j++) {
			QueenKingTropism[i][j]=
				(8 * (_MIN(abs(GetX(i)-GetX(j)), abs(GetY(i)-GetY(j)))) );
			BishopKingTropism[i][j]=
				(8 * (min(abs(GetX(i)-GetX(j)), abs(GetY(i)-GetY(j)))) );
			KnightKingTropism[i][j]=
				(12*(5-(abs(GetX(j)-GetX(i))+abs(GetY(j)-GetY(i)))));
			RookKingTropism[i][j]=
				(8 * (min(abs(GetX(i)-GetX(j)), abs(GetY(i)-GetY(j)))) );
			KingKingTropism[i][j]=
				(16*(5-(abs(GetX(j)-GetX(i))+abs(GetY(j)-GetY(i)))));
			TropismNear[i][j]=
				7-(min(abs(GetX(j)-GetX(i)),abs(GetY(j)-GetY(i))));
			TropismFar[i][j]=
				(min(abs(GetX(j)-GetX(i)),abs(GetY(j)-GetY(i))));
			SameDiagonal[i][j]=(((abs(i-j)%9)==0) || ((abs(i-j)%11)==0));
			KnightAttacks[i][j]=
			  (	abs(GetX(i)-GetX(j)==2) || abs(GetY(i)-GetY(j)==1) ||
					abs(GetX(i)-GetX(j)==1) || abs(GetY(i)-GetY(j)==2));
		}
	}
	for (i=1; i<8; i++) {
		for (j=1; j<8; j++) {
			BlackPawnAdvance[i*10+j]=WhitePawnAdvance[(9-i)*10+(9-j)];
		}
	}
#ifdef POSITIONALEVAL
	for (i=0; i<=60; i++) Segments[i]=0;
#endif
}

int
TSearcher::GetQuickMoveListWithChecks(TPosition InPosition, TMoveArray MoveArray)
{
	TMoveArray AllMoveArray;
	TPosition NewPosition;
	int AllMoveCount = GetMoveList(InPosition, AllMoveArray);
	int NewMoveCount = 0;
	for (int i=1; i<AllMoveCount; i++) 
	{
		if (AllMoveArray[i].Capture != EMPTY)
		{
			//MoveArray[++NewMoveCount] = AllMoveArray[i];
		}
		else
		{
			if (MakeMove(InPosition, AllMoveArray[i], NewPosition))
			{
				if (IsCheck(NewPosition))
				{
					MoveArray[++NewMoveCount] = AllMoveArray[i];
				}
			}
		}
	}

	return NewMoveCount;
}

int
TSearcher::GetQuickMoveList(TPosition InPosition, TMoveArray MoveArray)
{
#ifdef TESTING
	int t1 = GetTickCount();
#endif
	int Score, u, v;
	register POSITIONELEMENT* Position=InPosition;
	unsigned int i, j;
	int Square;
	POSITIONELEMENT* SquarePointer;
	int x, y;
	Amount=0;

	if (Position[MOVER]==WHITE) {
		for (j=1; j<=Position[WHITEPAWNS]; j++) {
				Square=Position[WHITEPAWNS+j];
				SquarePointer=Position+Square;
				x=GetFile[Square];
				y=GetRank[Square];
				if (y>=7) {
					if (*(SquarePointer+1)==EMPTY) CreateMove4(Square, Square+1, QUEEN);
					if (x<8 && *(SquarePointer+11)>EMPTY) CreateMove4(Square, Square+11, QUEEN);
					if (x>1 && *(SquarePointer-9)>EMPTY) CreateMove4(Square, Square-9, QUEEN);
				} else {
					if (x<8 && *(SquarePointer+11)>EMPTY) CreateMove(Square, Square+11);
					if (x>1 && *(SquarePointer-9)>EMPTY) CreateMove(Square, Square-9);
					if (y==5 && x>1 && x-1==Position[ENPAWN]) CreateMove(Square, Square-9);
					if (y==5 && x<8 && x+1==Position[ENPAWN]) CreateMove(Square, Square+11);
				}
		}
		for (j=1; j<=Position[WHITEKNIGHTS]; j++) {
				Square=Position[WHITEKNIGHTS+j];
				SquarePointer=Position+Square;
				x=GetFile[Square];
				y=GetRank[Square];
				if (x<8 && y>2 && *(SquarePointer+8)>EMPTY) CreateMove(Square, Square+8);
				if (x>1 && y<7 && *(SquarePointer-8)>EMPTY) CreateMove(Square, Square-8);
				if (x<8 && y<7 && *(SquarePointer+12)>EMPTY) CreateMove(Square, Square+12);
				if (x>1 && y>2 && *(SquarePointer-12)>EMPTY) CreateMove(Square, Square-12);
				if (x<7 && y>1 && *(SquarePointer+19)>EMPTY) CreateMove(Square, Square+19);
				if (x>2 && y<8 && *(SquarePointer-19)>EMPTY) CreateMove(Square, Square-19);
				if (x<7 && y<8 && *(SquarePointer+21)>EMPTY) CreateMove(Square, Square+21);
				if (x>2 && y>1 && *(SquarePointer-21)>EMPTY) CreateMove(Square, Square-21);
		}
		Square=Position[WKINGPOSITION];
		SquarePointer=Position+Square;
		x=GetFile[Square];
		y=GetRank[Square];
		if (x>1 && *(SquarePointer-10)>EMPTY) CreateMove(Square, Square-10);
		if (x<8 && *(SquarePointer+10)>EMPTY) CreateMove(Square, Square+10);
		if (y>1 && *(SquarePointer-1)>EMPTY) CreateMove(Square, Square-1);
		if (y<8 && *(SquarePointer+1)>EMPTY) CreateMove(Square, Square+1);
		if (x>1 && y>1 && *(SquarePointer-11)>EMPTY) CreateMove(Square, Square-11);
		if (x<8 && y<8 && *(SquarePointer+11)>EMPTY) CreateMove(Square, Square+11);
		if (x>1 && y<8 && *(SquarePointer-9)>EMPTY) CreateMove(Square, Square-9);
		if (x<8 && y>1 && *(SquarePointer+9)>EMPTY) CreateMove(Square, Square+9);
		for (j=1; j<=Position[WHITEROOKS]; j++) {
				Square=Position[WHITEROOKS+j];
						  for (i=Square+10; i<90 ; i+=10)
								  if (Position[i]>EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]<EMPTY) break;
						  for (i=Square-10; i>9 ; i-=10)
								  if (Position[i]>EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]<EMPTY) break;
						  for (i=Square+1; Valid[i] ; i++)
								  if (Position[i]>EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]<EMPTY) break;
						  for (i=Square-1; Valid[i] ; i--)
								  if (Position[i]>EMPTY) {
									 CreateMove(Square, i);
									 break;
								  } else if (Position[i]<EMPTY) break;
		}
		for (j=1; j<=Position[WHITEBISHOPS]; j++) {
				Square=Position[WHITEBISHOPS+j];
						  for (i=Square+11; Valid[i] ; i+=11)
								  if (Position[i]>EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]<EMPTY) break;
						  for (i=Square-11; Valid[i] ; i-=11)
								  if (Position[i]>EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]<EMPTY) break;
						  for (i=Square-9; Valid[i] ; i-=9)
								  if (Position[i]>EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]<EMPTY) break;
						  for (i=Square+9; Valid[i] ; i+=9)
								  if (Position[i]>EMPTY) {
									 CreateMove(Square, i);
									 break;
								  } else if (Position[i]<EMPTY) break;
		}
		for (j=1; j<=Position[WHITEQUEENS]; j++) {
				Square=Position[WHITEQUEENS+j];
						  for (i=Square+10; i<90 ; i+=10)
								  if (Position[i]>EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]<EMPTY) break;
						  for (i=Square-10; i>9 ; i-=10)
								  if (Position[i]>EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]<EMPTY) break;
						  for (i=Square+1; Valid[i] ; i++)
								  if (Position[i]>EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]<EMPTY) break;
						  for (i=Square-1; Valid[i] ; i--)
								  if (Position[i]>EMPTY) {
									 CreateMove(Square, i);
									 break;
								  } else if (Position[i]<EMPTY) break;
						  for (i=Square+11; Valid[i] ; i+=11)
								  if (Position[i]>EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]<EMPTY) break;
						  for (i=Square-11; Valid[i] ; i-=11)
								  if (Position[i]>EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]<EMPTY) break;
						  for (i=Square-9; Valid[i] ; i-=9)
								  if (Position[i]>EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]<EMPTY) break;
						  for (i=Square+9; Valid[i] ; i+=9)
								  if (Position[i]>EMPTY) {
									 CreateMove(Square, i);
									 break;
								  } else if (Position[i]<EMPTY) break;
		}
	} else {
		for (j=1; j<=Position[BLACKPAWNS]; j++) {
				Square=Position[BLACKPAWNS+j];
				SquarePointer=Position+Square;
				x=GetFile[Square];
				y=GetRank[Square];
				if (y<=2) {
					if (*(SquarePointer-1)==EMPTY) CreateMove4(Square, Square-1, QUEEN);
					if (x<8 && *(SquarePointer+9)<EMPTY) CreateMove4(Square, Square+9, QUEEN);
					if (x>1 && *(SquarePointer-11)<EMPTY) CreateMove4(Square, Square-11, QUEEN);
				} else {
					if (x<8 && *(SquarePointer+9)<EMPTY) CreateMove(Square, Square+9);
					if (x>1 && *(SquarePointer-11)<EMPTY) CreateMove(Square, Square-11);
					if (y==4 && x>1 && x-1==Position[ENPAWN]) CreateMove(Square, Square-11);
					if (y==4 && x<8 && x+1==Position[ENPAWN]) CreateMove(Square, Square+9);
				}
		}
		for (j=1; j<=Position[BLACKKNIGHTS]; j++) {
				Square=Position[BLACKKNIGHTS+j];
				SquarePointer=Position+Square;
				x=GetFile[Square];
				y=GetRank[Square];
				if (x<8 && y>2 && *(SquarePointer+8)<EMPTY) CreateMove(Square, Square+8);
				if (x>1 && y<7 && *(SquarePointer-8)<EMPTY) CreateMove(Square, Square-8);
				if (x<8 && y<7 && *(SquarePointer+12)<EMPTY) CreateMove(Square, Square+12);
				if (x>1 && y>2 && *(SquarePointer-12)<EMPTY) CreateMove(Square, Square-12);
				if (x<7 && y>1 && *(SquarePointer+19)<EMPTY) CreateMove(Square, Square+19);
				if (x>2 && y<8 && *(SquarePointer-19)<EMPTY) CreateMove(Square, Square-19);
				if (x<7 && y<8 && *(SquarePointer+21)<EMPTY) CreateMove(Square, Square+21);
				if (x>2 && y>1 && *(SquarePointer-21)<EMPTY) CreateMove(Square, Square-21);
		}
		Square=Position[BKINGPOSITION];
		SquarePointer=Position+Square;
		x=GetFile[Square];
		y=GetRank[Square];
		if (x>1 && *(SquarePointer-10)<EMPTY) CreateMove(Square, Square-10);
		if (x<8 && *(SquarePointer+10)<EMPTY) CreateMove(Square, Square+10);
		if (y>1 && *(SquarePointer-1)<EMPTY) CreateMove(Square, Square-1);
		if (y<8 && *(SquarePointer+1)<EMPTY) CreateMove(Square, Square+1);
		if (x>1 && y>1 && *(SquarePointer-11)<EMPTY) CreateMove(Square, Square-11);
		if (x<8 && y<8 && *(SquarePointer+11)<EMPTY) CreateMove(Square, Square+11);
		if (x>1 && y<8 && *(SquarePointer-9)<EMPTY) CreateMove(Square, Square-9);
		if (x<8 && y>1 && *(SquarePointer+9)<EMPTY) CreateMove(Square, Square+9);
		for (j=1; j<=Position[BLACKROOKS]; j++) {
			  Square=Position[BLACKROOKS+j];
			  for (i=Square+10; i<90 ; i+=10)
					if (Position[i]<EMPTY) {
						 CreateMove(Square, i);
						 break;
					} else if (Position[i]>EMPTY) break;
			  for (i=Square-10; i>9 ; i-=10)
					 if (Position[i]<EMPTY) {
						  CreateMove(Square, i);
						  break;
					 } else if (Position[i]>EMPTY) break;
			  for (i=Square+1; Valid[i] ; i++)
					 if (Position[i]<EMPTY) {
						  CreateMove(Square, i);
						  break;
					 } else if (Position[i]>EMPTY) break;
			  for (i=Square-1; Valid[i] ; i--)
					 if (Position[i]<EMPTY) {
						  CreateMove(Square, i);
						  break;
					 } else if (Position[i]>EMPTY) break;
		}
		for (j=1; j<=Position[BLACKBISHOPS]; j++) {
				Square=Position[BLACKBISHOPS+j];
						  for (i=Square+11; Valid[i] ; i+=11)
								  if (Position[i]<EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]>EMPTY) break;
						  for (i=Square-11; Valid[i] ; i-=11)
								  if (Position[i]<EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]>EMPTY) break;
						  for (i=Square-9; Valid[i] ; i-=9)
								  if (Position[i]<EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]>EMPTY) break;
						  for (i=Square+9; Valid[i] ; i+=9)
								  if (Position[i]<EMPTY) {
									 CreateMove(Square, i);
									 break;
								  } else if (Position[i]>EMPTY) break;
		}
		for (j=1; j<=Position[BLACKQUEENS]; j++) {
				Square=Position[BLACKQUEENS+j];
						  for (i=Square+10; i<90 ; i+=10)
								  if (Position[i]<EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]>EMPTY) break;
						  for (i=Square-10; i>9 ; i-=10)
								  if (Position[i]<EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]>EMPTY) break;
						  for (i=Square+1; Valid[i] ; i++)
								  if (Position[i]<EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]>EMPTY) break;
						  for (i=Square-1; Valid[i] ; i--)
								  if (Position[i]<EMPTY) {
									 CreateMove(Square, i);
									 break;
								  } else if (Position[i]>EMPTY) break;
						  for (i=Square+11; Valid[i] ; i+=11)
								  if (Position[i]<EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]>EMPTY) break;
						  for (i=Square-11; Valid[i] ; i-=11)
								  if (Position[i]<EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]>EMPTY) break;
						  for (i=Square-9; Valid[i] ; i-=9)
								  if (Position[i]<EMPTY) {
									  CreateMove(Square, i);
									  break;
								  } else if (Position[i]>EMPTY) break;
						  for (i=Square+9; Valid[i] ; i+=9)
								  if (Position[i]<EMPTY) {
									 CreateMove(Square, i);
									 break;
								  } else if (Position[i]>EMPTY) break;
		}
	}

#ifdef TESTING
	int t2 = GetTickCount() - t1;
	TotalGetQuickMoveListCalls++;
	TotalGetQuickMoveListMillis += t2;
#endif
	return Amount;
}

int IsAttackedLoop;

bool inline
TSearcher::IsAttacked(TPosition Position, int FromSquare, int MoveDir, int TargetSquare)
{
#ifdef TESTING
	int t1 = GetTickCount();
#endif

	bool Attacked = false;

	for (IsAttackedLoop=FromSquare + MoveDir; Valid[IsAttackedLoop]; IsAttackedLoop+=MoveDir )
	{
		if (Position[IsAttackedLoop] != EMPTY)
		{
			Attacked = (IsAttackedLoop == TargetSquare);
			break;
		}
	}

#ifdef TESTING
	int t2 = GetTickCount() - t1;
	TotalIsAttackedCalls++;
	TotalIsAttackedMillis += t2;
#endif
	return Attacked;
}

int inline
TSearcher::FirstPieceOnLineViaSquare(TPosition Position, int FromSquare, int MoveDir, int ViaSquare, int BlockSquare)
{
#ifdef TESTING
	int t1 = GetTickCount();
#endif

	// What is the first piece we come across in the given direction?
	// Return EMPTY if it does not pass through ViaSquare before hitting a piece
	// ViaSquare may be populated, but the piece will be ignored
	// Hitting Blocksquare also returns false (this is the square where a piece may have been moved to but is not represented on board)

	ViaSquareHit = false;

	for (FirstPieceLoop=FromSquare; Valid[FirstPieceLoop]; FirstPieceLoop+=MoveDir)
	{
		if ((Position[FirstPieceLoop] != EMPTY || FirstPieceLoop == BlockSquare) && FirstPieceLoop != ViaSquare)
		{
			if (ViaSquareHit)
			{
				goto returnnow;
			}
			break;
		}
		ViaSquareHit = ViaSquareHit || (FirstPieceLoop == ViaSquare);
	}

#ifdef TESTING
	int t2 = GetTickCount() - t1;
	TotalFirstPieceCalls++;
	TotalFirstPieceMillis += t2;
#endif
	return EMPTY;

returnnow:
	return Position[FirstPieceLoop];

}

int IDC_KingColour;
int IDC_FirstPiece;
int IDC_Queen;
int IDC_Rook;
int IDC_Bishop;

bool inline
TSearcher::IsDiscoveredCheck(TPosition Position, int VacatedSquare, int KingSquare, int BlockSquare)
{
#ifdef TESTING
	int t1 = GetTickCount();
#endif

	IDC_KingColour = (Position[KingSquare] < EMPTY ? WHITE : BLACK);
	IDC_FirstPiece;
	IDC_Queen = QUEEN + (IDC_KingColour==WHITE ? 100 : 0);
	IDC_Rook = ROOK + (IDC_KingColour==WHITE ? 100 : 0);
	IDC_Bishop = BISHOP + (IDC_KingColour==WHITE ? 100 : 0);

	IDC_FirstPiece = FirstPieceOnLineViaSquare(Position, KingSquare + MOVEDIR_LEFT, MOVEDIR_LEFT, VacatedSquare, BlockSquare);
	if (IDC_FirstPiece == IDC_Queen || IDC_FirstPiece == IDC_Rook)
	{
		goto returntrue;
	}
	IDC_FirstPiece = FirstPieceOnLineViaSquare(Position, KingSquare + MOVEDIR_RIGHT, MOVEDIR_RIGHT, VacatedSquare, BlockSquare);
	if (IDC_FirstPiece == IDC_Queen || IDC_FirstPiece == IDC_Rook)
	{
		goto returntrue;
	}
	IDC_FirstPiece = FirstPieceOnLineViaSquare(Position, KingSquare + MOVEDIR_DOWN, MOVEDIR_DOWN, VacatedSquare, BlockSquare);
	if (IDC_FirstPiece == IDC_Queen || IDC_FirstPiece == IDC_Rook)
	{
		goto returntrue;
	}
	IDC_FirstPiece = FirstPieceOnLineViaSquare(Position, KingSquare + MOVEDIR_UP, MOVEDIR_UP, VacatedSquare, BlockSquare);
	if (IDC_FirstPiece == IDC_Queen || IDC_FirstPiece == IDC_Rook)
	{
		goto returntrue;
	}
	IDC_FirstPiece = FirstPieceOnLineViaSquare(Position, KingSquare + MOVEDIR_UPLEFT, MOVEDIR_UPLEFT, VacatedSquare, BlockSquare);
	if (IDC_FirstPiece == IDC_Queen || IDC_FirstPiece == IDC_Bishop)
	{
		goto returntrue;
	}
	IDC_FirstPiece = FirstPieceOnLineViaSquare(Position, KingSquare + MOVEDIR_UPRIGHT, MOVEDIR_UPRIGHT, VacatedSquare, BlockSquare);
	if (IDC_FirstPiece == IDC_Queen || IDC_FirstPiece == IDC_Bishop)
	{
		goto returntrue;
	}
	IDC_FirstPiece = FirstPieceOnLineViaSquare(Position, KingSquare + MOVEDIR_DOWNLEFT, MOVEDIR_DOWNLEFT, VacatedSquare, BlockSquare);
	if (IDC_FirstPiece == IDC_Queen || IDC_FirstPiece == IDC_Bishop)
	{
		goto returntrue;
	}
	IDC_FirstPiece = FirstPieceOnLineViaSquare(Position, KingSquare + MOVEDIR_DOWNRIGHT, MOVEDIR_DOWNRIGHT, VacatedSquare, BlockSquare);
	if (IDC_FirstPiece == IDC_Queen || IDC_FirstPiece == IDC_Bishop)
	{
		goto returntrue;
	}

#ifdef TESTING
	int t2 = GetTickCount() - t1;
	TotalIsDiscoveredCheckCalls++;
	TotalIsDiscoveredCheckMillis += t2;
#endif
	return false;

returntrue:
	return true;
}

int ICM_EnemyKingSquare;
int ICM_ToSquare;
int ICM_ToX;
int ICM_ToY;
bool ICM_CheckingMove;
int ICM_ActualPiece;
int ICM_OriginalPiece;

TPosition IsCheckingMovePosition;
int IsCheckingMoveReturnValue;

bool inline
TSearcher::IsCheckingMove(TPosition Position, TMove& Move)
{
#ifdef TESTING
	int t1 = GetTickCount();
#endif

	MakeMoveQuick(Position, Move, IsCheckingMovePosition);
	IsCheckingMoveReturnValue = IsCheck(IsCheckingMovePosition);

	/*TPosition NewPos;
	MakeMove(Position, Move, NewPos);
	int NewVal = IsCheck(NewPos);

	assert (NewVal == IsCheckingMoveReturnValue);*/

#ifdef TESTING
	int t2 = GetTickCount() - t1;
	TotalIsCheckingMoveCalls++;
	TotalIsCheckingMoveMillis += t2;
#endif

	return (IsCheckingMoveReturnValue == 1);
}

bool inline
TSearcher::IsCheckingMoveStandard(TPosition Position, TMove& Move)
{
#ifdef TESTING
	int t1 = GetTickCount();
#endif
	POSITIONELEMENT *FromPiece=Position+Move.From;
	ICM_ToSquare = Move.To;
	ICM_ToX = GetX(Move.To);
	ICM_ToY = GetY(Move.To);

	ICM_CheckingMove = false;

	ICM_ActualPiece = *FromPiece;

	if (ICM_ActualPiece == WP && ICM_ToY == 8)
	{
		ICM_ActualPiece = Move.PromotionPiece;
	}
	else
	if (ICM_ActualPiece == BP && ICM_ToY == 1)
	{
		ICM_ActualPiece = Move.PromotionPiece;
	}
		
	ICM_OriginalPiece = Position[Move.From];
	Position[Move.From] = EMPTY;

	if (Position[MOVER] == WHITE)
	{
		ICM_EnemyKingSquare = Position[BKINGPOSITION];
		if (Move.From == 51 && *FromPiece == WK)
		{
			if (ICM_ToSquare == 31)
			{
				ICM_CheckingMove = IsAttacked(Position, 61, MOVEDIR_UP, ICM_EnemyKingSquare);
				goto done;
			}

			if (ICM_ToSquare == 71)
			{
				ICM_CheckingMove = IsAttacked(Position, 41, MOVEDIR_UP, ICM_EnemyKingSquare);
				goto done;
			}
		}

		if (IsDiscoveredCheck(Position, Move.From, ICM_EnemyKingSquare, ICM_ToSquare))
		{
			ICM_CheckingMove = true;
			goto done;
		}

		switch (ICM_ActualPiece)
		{
			case WP :
				if (ICM_ToSquare-9 == ICM_EnemyKingSquare || ICM_ToSquare+11 == ICM_EnemyKingSquare)
				{
					ICM_CheckingMove = true;
					goto done;
				}
				if (ICM_ToY==6 && ICM_ToX==Position[ENPAWN])
				{
					Position[ICM_ToX*10+5] = EMPTY;
					bool DoesCheck =
						IsDiscoveredCheck(Position, Move.From, ICM_EnemyKingSquare, ICM_ToSquare) ||
						IsDiscoveredCheck(Position, ICM_ToX*10+5, ICM_EnemyKingSquare, ICM_ToSquare);
					Position[ICM_ToX*10+5] = BP;

					ICM_CheckingMove = DoesCheck;
					goto done;
				}
				break;
			case WR :
					ICM_CheckingMove =  
						IsAttacked(Position, Move.To, MOVEDIR_LEFT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_RIGHT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_DOWN, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_UP, ICM_EnemyKingSquare);
					goto done;
				break;
			case WB :
					ICM_CheckingMove =  
						IsAttacked(Position, Move.To, MOVEDIR_UPLEFT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_UPRIGHT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_DOWNLEFT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_DOWNRIGHT, ICM_EnemyKingSquare);
					goto done;
				break;
			case WQ :
					ICM_CheckingMove =  
						IsAttacked(Position, Move.To, MOVEDIR_LEFT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_RIGHT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_DOWN, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_UP, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_UPLEFT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_UPRIGHT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_DOWNLEFT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_DOWNRIGHT, ICM_EnemyKingSquare);
					goto done;
				break;
			case WN :
					ICM_CheckingMove = 
						(ICM_ToX>2 && ICM_ToY>1 && ICM_ToSquare-21==ICM_EnemyKingSquare) ||
						(ICM_ToX>2 && ICM_ToY<8 && ICM_ToSquare-19==ICM_EnemyKingSquare) ||
						(ICM_ToX>1 && ICM_ToY>2 && ICM_ToSquare-12==ICM_EnemyKingSquare) ||
						(ICM_ToX>1 && ICM_ToY<7 && ICM_ToSquare-8==ICM_EnemyKingSquare) ||
						(ICM_ToX<7 && ICM_ToY<8 && ICM_ToSquare+21==ICM_EnemyKingSquare) ||
						(ICM_ToX<7 && ICM_ToY>1 && ICM_ToSquare+19==ICM_EnemyKingSquare) ||
						(ICM_ToX<8 && ICM_ToY<7 && ICM_ToSquare+12==ICM_EnemyKingSquare) ||
						(ICM_ToX<8 && ICM_ToY>2 && ICM_ToSquare+8==ICM_EnemyKingSquare);	
					goto done;
				break;
		}
	}
	else
	{
		ICM_EnemyKingSquare = Position[WKINGPOSITION];
		if (Move.From == 58 && *FromPiece == BK)
		{
			if (ICM_ToSquare == 38)
			{
				ICM_CheckingMove = IsAttacked(Position, 68, MOVEDIR_DOWN, ICM_EnemyKingSquare);
				goto done;
			}

			if (ICM_ToSquare == 78)
			{
				ICM_CheckingMove = IsAttacked(Position, 48, MOVEDIR_DOWN, ICM_EnemyKingSquare);
				goto done;
			}
		}

		if (IsDiscoveredCheck(Position, Move.From, ICM_EnemyKingSquare, ICM_ToSquare))
		{
			ICM_CheckingMove = true;
			goto done;
		}

		switch (ICM_ActualPiece)
		{
			case BP :
				if (ICM_ToSquare+9 == ICM_EnemyKingSquare || ICM_ToSquare-11 == ICM_EnemyKingSquare)
				{
					ICM_CheckingMove = true;
					goto done;
				}
				if (ICM_ToY==3 && ICM_ToX==Position[ENPAWN])
				{
					Position[ICM_ToX*10+4] = EMPTY;
					bool DoesCheck =
						IsDiscoveredCheck(Position, Move.From, ICM_EnemyKingSquare, ICM_ToSquare) ||
						IsDiscoveredCheck(Position, ICM_ToX*10+4, ICM_EnemyKingSquare, ICM_ToSquare);
					Position[ICM_ToX*10+4] = WP;

					ICM_CheckingMove = DoesCheck;
					goto done;
				}
				break;
			case BR :
					ICM_CheckingMove = 
						IsAttacked(Position, Move.To, MOVEDIR_LEFT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_RIGHT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_DOWN, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_UP, ICM_EnemyKingSquare);
					goto done;

				break;
			case BB :
					ICM_CheckingMove =  
						IsAttacked(Position, Move.To, MOVEDIR_UPLEFT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_UPRIGHT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_DOWNLEFT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_DOWNRIGHT, ICM_EnemyKingSquare);
					goto done;
				break;
			case BQ :
					ICM_CheckingMove =  
						IsAttacked(Position, Move.To, MOVEDIR_LEFT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_RIGHT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_DOWN, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_UP, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_UPLEFT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_UPRIGHT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_DOWNLEFT, ICM_EnemyKingSquare) ||
						IsAttacked(Position, Move.To, MOVEDIR_DOWNRIGHT, ICM_EnemyKingSquare);
					goto done;
				break;
			case BN :
					ICM_CheckingMove = 
						(ICM_ToX>2 && ICM_ToY>1 && ICM_ToSquare-21==ICM_EnemyKingSquare) ||
						(ICM_ToX>2 && ICM_ToY<8 && ICM_ToSquare-19==ICM_EnemyKingSquare) ||
						(ICM_ToX>1 && ICM_ToY>2 && ICM_ToSquare-12==ICM_EnemyKingSquare) ||
						(ICM_ToX>1 && ICM_ToY<7 && ICM_ToSquare-8==ICM_EnemyKingSquare) ||
						(ICM_ToX<7 && ICM_ToY<8 && ICM_ToSquare+21==ICM_EnemyKingSquare) ||
						(ICM_ToX<7 && ICM_ToY>1 && ICM_ToSquare+19==ICM_EnemyKingSquare) ||
						(ICM_ToX<8 && ICM_ToY<7 && ICM_ToSquare+12==ICM_EnemyKingSquare) ||
						(ICM_ToX<8 && ICM_ToY>2 && ICM_ToSquare+8==ICM_EnemyKingSquare);	
					goto done;
				break;
		}

	}

done:
#ifdef TESTING
	int t2 = GetTickCount() - t1;
	TotalIsCheckingMoveCalls++;
	TotalIsCheckingMoveMillis += t2;
#endif
	Position[Move.From] = ICM_OriginalPiece;

	assert(ICM_CheckingMove == (IsCheck(Position) == 1));
	return ICM_CheckingMove;
}

int
TSearcher::GetMoveList(TPosition InPosition, TMoveArray MoveArray)
{
#ifdef TESTING
	int t1 = GetTickCount();
#endif
	int Score;

	register POSITIONELEMENT* Position=InPosition;
	int i, u, v;
	POSITIONELEMENT* SquarePointer;
	int x, y;
	Amount=0;

	int LastMovePiece=Position[LASTMOVESQUARE];
	if (Position[MOVER]==WHITE) {
		POSITIONELEMENT* q=Position+WHITEPAWNS;
		for (q+=*q; q!=Position+WHITEPAWNS; q--) {
				SquarePointer=Position+*q;
				x=GetFile[*q];
				y=GetRank[*q];
				if (*(SquarePointer+1)==EMPTY) {
							 if (y==7) {
								CreateMove3(*q, *q+1, QUEEN);
								CreateMove3(*q, *q+1, BISHOP);
								CreateMove3(*q, *q+1, ROOK);
								CreateMove3(*q, *q+1, KNIGHT);
							 } else {
								CreateMove2(*q, *q+1);
							 }
							 if (y==2 && *(SquarePointer+2)==EMPTY) CreateMove2(*q, *q+2);
						  }
						  if (x<8 && *(SquarePointer+11)>EMPTY) {
							 if (y==7) {
								CreateMove3(*q, *q+11, QUEEN);
								CreateMove3(*q, *q+11, BISHOP);
								CreateMove3(*q, *q+11, ROOK);
								CreateMove3(*q, *q+11, KNIGHT);
							 } else {
								CreateMove2(*q, *q+11);
							 }
						  }
						  if (x>1 && *(SquarePointer-9)>EMPTY) {
							 if (y==7) {
								CreateMove3(*q, *q-9, QUEEN);
								CreateMove3(*q, *q-9, BISHOP);
								CreateMove3(*q, *q-9, ROOK);
								CreateMove3(*q, *q-9, KNIGHT);
							 } else {
								CreateMove2(*q, *q-9);
							 }
						  }
						  if (y==5 && x>1 && x-1==Position[ENPAWN]) CreateMove2(*q, *q-9);
						  if (y==5 && x<8 && x+1==Position[ENPAWN]) CreateMove2(*q, *q+11);
		}
		for (q+=(WHITEKNIGHTS-WHITEPAWNS), q+=*q; q!=Position+WHITEKNIGHTS; q--) {
				SquarePointer=Position+*q;
				x=GetFile[*q];
				y=GetRank[*q];
				if (x<8 && y>2 && *(SquarePointer+8)>=EMPTY) CreateMove2(*q, *q+8);
				if (x>1 && y<7 && *(SquarePointer-8)>=EMPTY) CreateMove2(*q, *q-8);
				if (x<8 && y<7 && *(SquarePointer+12)>=EMPTY) CreateMove2(*q, *q+12);
				if (x>1 && y>2 && *(SquarePointer-12)>=EMPTY) CreateMove2(*q, *q-12);
				if (x<7 && y>1 && *(SquarePointer+19)>=EMPTY) CreateMove2(*q, *q+19);
				if (x>2 && y<8 && *(SquarePointer-19)>=EMPTY) CreateMove2(*q, *q-19);
				if (x<7 && y<8 && *(SquarePointer+21)>=EMPTY) CreateMove2(*q, *q+21);
				if (x>2 && y>1 && *(SquarePointer-21)>=EMPTY) CreateMove2(*q, *q-21);
		}
		for (q+=(WHITEBISHOPS-WHITEKNIGHTS), q+=*q; q!=Position+WHITEBISHOPS; q--) {
				for (i=*q+11; Valid[i] ; i+=11)
				  if (Position[i]>=EMPTY) {
					  CreateMove2(*q, i);
					  if (Position[i]!=EMPTY) break;
				  } else break;
				for (i=*q-11; Valid[i] ; i-=11)
				  if (Position[i]>=EMPTY) {
					  CreateMove2(*q, i);
					  if (Position[i]!=EMPTY) break;
				  } else break;
				for (i=*q-9; Valid[i] ; i-=9)
				  if (Position[i]>=EMPTY) {
					  CreateMove2(*q, i);
					  if (Position[i]!=EMPTY) break;
				  } else break;
				for (i=*q+9; Valid[i] ; i+=9)
				  if (Position[i]>=EMPTY) {
					 CreateMove2(*q, i);
					 if (Position[i]!=EMPTY) break;
				  } else break;
				}
		for (q+=(WHITEROOKS-WHITEBISHOPS), q+=*q; q!=Position+WHITEROOKS; q--) {
				for (i=*q+10; i<90 ; i+=10)
				  if (Position[i]>=EMPTY) {
					  CreateMove2(*q, i);
					  if (Position[i]!=EMPTY) break;
				  } else break;
				for (i=*q-10; i>9 ; i-=10)
				  if (Position[i]>=EMPTY) {
					  CreateMove2(*q, i);
					  if (Position[i]!=EMPTY) break;
				  } else break;
				for (i=*q+1; Valid[i] ; i++)
					 if (Position[i]>=EMPTY) {
					  CreateMove2(*q, i);
					  if (Position[i]!=EMPTY) break;
				  } else break;
				for (i=*q-1; Valid[i] ; i--)
					  if (Position[i]>=EMPTY) {
						CreateMove2(*q, i);
						if (Position[i]!=EMPTY) break;
					  } else break;
		}
		for (q+=(WHITEQUEENS-WHITEROOKS), q+=*q; q!=Position+WHITEQUEENS; q--) {
				for (i=*q+10; i<90 ; i+=10)
								  if (Position[i]>=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q-10; i>9 ; i-=10)
								  if (Position[i]>=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q+1; Valid[i] ; i++)
								  if (Position[i]>=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q-1; Valid[i] ; i--)
								  if (Position[i]>=EMPTY) {
									 CreateMove2(*q, i);
									 if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q+11; Valid[i] ; i+=11)
								  if (Position[i]>=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q-11; Valid[i] ; i-=11)
								  if (Position[i]>=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q-9; Valid[i] ; i-=9)
								  if (Position[i]>=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q+9; Valid[i] ; i+=9)
								  if (Position[i]>=EMPTY) {
									 CreateMove2(*q, i);
									 if (Position[i]!=EMPTY) break;
								  } else break;
		}
		q+=(WKINGPOSITION-WHITEQUEENS);
		SquarePointer=Position+*q;
		x=GetFile[*q];
		y=GetRank[*q];
		if (x>1 && *(SquarePointer-10)>=EMPTY) CreateMove2(*q, *q-10);
		if (x<8 && *(SquarePointer+10)>=EMPTY) CreateMove2(*q, *q+10);
		if (y>1 && *(SquarePointer-1)>=EMPTY) CreateMove2(*q, *q-1);
		if (y<8 && *(SquarePointer+1)>=EMPTY) CreateMove2(*q, *q+1);
		if (x>1 && y>1 && *(SquarePointer-11)>=EMPTY) CreateMove2(*q, *q-11);
		if (x<8 && y<8 && *(SquarePointer+11)>=EMPTY) CreateMove2(*q, *q+11);
		if (x>1 && y<8 && *(SquarePointer-9)>=EMPTY) CreateMove2(*q, *q-9);
		if (x<8 && y>1 && *(SquarePointer+9)>=EMPTY) CreateMove2(*q, *q+9);
		if (!Position[WKINGMOVED]) {
			 if (!IsCheck(Position)) {
				if (!Position[WROOK8MOVED]) {
				  if (Position[61]==EMPTY && Position[71]==EMPTY) {
					  Position[61]=WK;
					  Position[51]=EMPTY;
					  Position[WKINGPOSITION]=61;
					  int NoThroughCheck=!IsCheck(Position);
					  Position[51]=WK;
					  Position[61]=EMPTY;
					  Position[WKINGPOSITION]=51;
					  if (NoThroughCheck) CreateMove2(51, 71);
				  }
				}
				if (!Position[WROOK1MOVED]) {
				  if (Position[41]==EMPTY && Position[31]==EMPTY && Position[21]==EMPTY) {
					  Position[41]=WK;
					  Position[51]=EMPTY;
					  Position[WKINGPOSITION]=41;
					  int NoThroughCheck=!IsCheck(Position);
					  Position[51]=WK;
					  Position[41]=EMPTY;
					  Position[WKINGPOSITION]=51;
					  if (NoThroughCheck) CreateMove2(51, 31);
				  }
				}
			 }
		}
	} else {
		POSITIONELEMENT* q=Position+BLACKPAWNS;
		for (q+=*q; q!=Position+BLACKPAWNS; q--) {
				SquarePointer=Position+*q;
				x=GetFile[*q];
				y=GetRank[*q];
				if (*(SquarePointer-1)==EMPTY) {
							  if (y==2)	{
									CreateMove3(*q, *q-1, QUEEN);
									CreateMove3(*q, *q-1, BISHOP);
									CreateMove3(*q, *q-1, ROOK);
									CreateMove3(*q, *q-1, KNIGHT);
							  } else {
									CreateMove2(*q, *q-1);
							  }
							  if (y==7 && *(SquarePointer-2)==EMPTY)
								  CreateMove2(*q, *q-2);
						  }
						  if (x<8 && *(SquarePointer+9)<EMPTY) {
							  if (y==2) {
									CreateMove3(*q, *q+9, QUEEN);
									CreateMove3(*q, *q+9, BISHOP);
									CreateMove3(*q, *q+9, ROOK);
									CreateMove3(*q, *q+9, KNIGHT);
							  } else {
									CreateMove2(*q, *q+9);
							  }
						  }
						  if (x>1 && *(SquarePointer-11)<EMPTY) {
							  if (y==2) {
									CreateMove3(*q, *q-11, QUEEN);
									CreateMove3(*q, *q-11, BISHOP);
									CreateMove3(*q, *q-11, ROOK);
									CreateMove3(*q, *q-11, KNIGHT);
							  } else {
									CreateMove2(*q, *q-11);
							  }
						  }
						  if (y==4 && x>1 && x-1==Position[ENPAWN]) CreateMove2(*q, *q-11);
						  if (y==4 && x<8 && x+1==Position[ENPAWN]) CreateMove2(*q, *q+9);
		}
		for (q+=(BLACKKNIGHTS-BLACKPAWNS), q+=*q; q!=Position+BLACKKNIGHTS; q--) {
				SquarePointer=Position+*q;
				x=GetFile[*q];
				y=GetRank[*q];
				if (x<8 && y>2 && *(SquarePointer+8)<=EMPTY) CreateMove2(*q, *q+8);
				if (x>1 && y<7 && *(SquarePointer-8)<=EMPTY) CreateMove2(*q, *q-8);
				if (x<8 && y<7 && *(SquarePointer+12)<=EMPTY) CreateMove2(*q, *q+12);
				if (x>1 && y>2 && *(SquarePointer-12)<=EMPTY) CreateMove2(*q, *q-12);
				if (x<7 && y>1 && *(SquarePointer+19)<=EMPTY) CreateMove2(*q, *q+19);
				if (x>2 && y<8 && *(SquarePointer-19)<=EMPTY) CreateMove2(*q, *q-19);
				if (x<7 && y<8 && *(SquarePointer+21)<=EMPTY) CreateMove2(*q, *q+21);
				if (x>2 && y>1 && *(SquarePointer-21)<=EMPTY) CreateMove2(*q, *q-21);
		}
		for (q+=(BLACKBISHOPS-BLACKKNIGHTS), q+=*q; q!=Position+BLACKBISHOPS; q--) {
				for (i=*q+11; Valid[i] ; i+=11)
								  if (Position[i]<=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q-11; Valid[i] ; i-=11)
								  if (Position[i]<=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q-9; Valid[i] ; i-=9)
								  if (Position[i]<=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q+9; Valid[i] ; i+=9)
								  if (Position[i]<=EMPTY) {
									 CreateMove2(*q, i);
									 if (Position[i]!=EMPTY) break;
								  } else break;
		}
		for (q+=(BLACKROOKS-BLACKBISHOPS), q+=*q; q!=Position+BLACKROOKS; q--) {
				for (i=*q+10; i<90 ; i+=10)
								  if (Position[i]<=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q-10; i>9 ; i-=10)
								  if (Position[i]<=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q+1; Valid[i] ; i++)
								  if (Position[i]<=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q-1; Valid[i] ; i--)
								  if (Position[i]<=EMPTY) {
									 CreateMove2(*q, i);
									 if (Position[i]!=EMPTY) break;
								  } else break;
		}
		for (q+=(BLACKQUEENS-BLACKROOKS), q+=*q; q!=Position+BLACKQUEENS; q--) {
				for (i=*q+10; i<90 ; i+=10)
								  if (Position[i]<=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q-10; i>9 ; i-=10)
								  if (Position[i]<=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q+1; Valid[i] ; i++)
								  if (Position[i]<=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q-1; Valid[i] ; i--)
								  if (Position[i]<=EMPTY) {
									 CreateMove2(*q, i);
									 if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q+11; Valid[i] ; i+=11)
								  if (Position[i]<=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q-11; Valid[i] ; i-=11)
								  if (Position[i]<=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q-9; Valid[i] ; i-=9)
								  if (Position[i]<=EMPTY) {
									  CreateMove2(*q, i);
									  if (Position[i]!=EMPTY) break;
								  } else break;
						  for (i=*q+9; Valid[i] ; i+=9)
								  if (Position[i]<=EMPTY) {
									 CreateMove2(*q, i);
									 if (Position[i]!=EMPTY) break;
								  } else break;
		}
		q+=(BKINGPOSITION-BLACKQUEENS);
		SquarePointer=Position+*q;
		x=GetFile[*q];
		y=GetRank[*q];
		if (x>1 && *(SquarePointer-10)<=EMPTY) CreateMove2(*q, *q-10);
		if (x<8 && *(SquarePointer+10)<=EMPTY) CreateMove2(*q, *q+10);
		if (y>1 && *(SquarePointer-1)<=EMPTY) CreateMove2(*q, *q-1);
		if (y<8 && *(SquarePointer+1)<=EMPTY) CreateMove2(*q, *q+1);
		if (x>1 && y>1 && *(SquarePointer-11)<=EMPTY) CreateMove2(*q, *q-11);
		if (x<8 && y<8 && *(SquarePointer+11)<=EMPTY) CreateMove2(*q, *q+11);
		if (x>1 && y<8 && *(SquarePointer-9)<=EMPTY) CreateMove2(*q, *q-9);
		if (x<8 && y>1 && *(SquarePointer+9)<=EMPTY) CreateMove2(*q, *q+9);
		if (!Position[BKINGMOVED]) {
			if (!IsCheck(Position)) {
				if (!Position[BROOK8MOVED]) {
					if (Position[68]==EMPTY && Position[78]==EMPTY) {
						Position[68]=BK;
						Position[58]=EMPTY;
						Position[BKINGPOSITION]=68;
						int NoThroughCheck=!IsCheck(Position);
						Position[58]=BK;
						Position[68]=EMPTY;
						Position[BKINGPOSITION]=58;
						if (NoThroughCheck) CreateMove2(58, 78);
					}
				}
				if (!Position[BROOK1MOVED]) {
					if (Position[48]==EMPTY && Position[38]==EMPTY && Position[28]==EMPTY) {
						Position[48]=BK;
						Position[58]=EMPTY;
						Position[BKINGPOSITION]=48;
						int NoThroughCheck=!IsCheck(Position);
						Position[58]=BK;
						Position[48]=EMPTY;
						Position[BKINGPOSITION]=58;
						if (NoThroughCheck) CreateMove2(58, 38);
					}
				}
			}
		}
	}

	for (i=1; i<=Amount; i++) 
	{
		if (MoveArray[i].From==PrincipalPath.Move[CurrentDepth].From && MoveArray[i].To==PrincipalPath.Move[CurrentDepth].To)  
		{
			TMove TempMove=MoveArray[i];
			for (int j=i-1; j>=1; j--) 
			{
				MoveArray[j+1]=MoveArray[j];
			}
			MoveArray[1]=TempMove;
		}
	}

#ifdef TESTING
	int t2 = GetTickCount() - t1;
	TotalGetMoveListCalls++;
	TotalGetMoveListMillis += t2;
#endif
	return Amount;
}

int 
TSearcher::GetCheckMoveListWithoutCaptures(TPosition InPosition, TMoveArray MoveArray)
{
#ifdef TESTING
	int t1 = GetTickCount();
#endif
	register POSITIONELEMENT* Position=InPosition;
	int i;
	POSITIONELEMENT* SquarePointer;
	int x, y;
	Amount=0;
	TMove TempMoveToTestCheck;
	int LastMovePiece=Position[LASTMOVESQUARE];
	if (Position[MOVER]==WHITE) {
		POSITIONELEMENT* q=Position+WHITEPAWNS;
		for (q+=*q; q!=Position+WHITEPAWNS; q--) {
				SquarePointer=Position+*q;
				x=GetFile[*q];
				y=GetRank[*q];
				if (*(SquarePointer+1)==EMPTY) {
							 if (y==7) {
								CreateCheckMovePromote(*q, *q+1, QUEEN);
							 } else {
								CreateCheckMove(*q, *q+1);
							 }
							 if (y==2 && *(SquarePointer+2)==EMPTY) CreateCheckMove(*q, *q+2);
						  }
		}
		for (q+=(WHITEKNIGHTS-WHITEPAWNS), q+=*q; q!=Position+WHITEKNIGHTS; q--) {
				SquarePointer=Position+*q;
				x=GetFile[*q];
				y=GetRank[*q];
				if (x<8 && y>2 && *(SquarePointer+8)==EMPTY) CreateCheckMove(*q, *q+8);
				if (x>1 && y<7 && *(SquarePointer-8)==EMPTY) CreateCheckMove(*q, *q-8);
				if (x<8 && y<7 && *(SquarePointer+12)==EMPTY) CreateCheckMove(*q, *q+12);
				if (x>1 && y>2 && *(SquarePointer-12)==EMPTY) CreateCheckMove(*q, *q-12);
				if (x<7 && y>1 && *(SquarePointer+19)==EMPTY) CreateCheckMove(*q, *q+19);
				if (x>2 && y<8 && *(SquarePointer-19)==EMPTY) CreateCheckMove(*q, *q-19);
				if (x<7 && y<8 && *(SquarePointer+21)==EMPTY) CreateCheckMove(*q, *q+21);
				if (x>2 && y>1 && *(SquarePointer-21)==EMPTY) CreateCheckMove(*q, *q-21);
		}
		for (q+=(WHITEBISHOPS-WHITEKNIGHTS), q+=*q; q!=Position+WHITEBISHOPS; q--) {
				for (i=*q+11; Valid[i] ; i+=11)
				  if (Position[i]==EMPTY) {
					  CreateCheckMove(*q, i);
				  } else break;
				for (i=*q-11; Valid[i] ; i-=11)
				  if (Position[i]==EMPTY) {
					  CreateCheckMove(*q, i);
				  } else break;
				for (i=*q-9; Valid[i] ; i-=9)
				  if (Position[i]==EMPTY) {
					  CreateCheckMove(*q, i);
				  } else break;
				for (i=*q+9; Valid[i] ; i+=9)
				  if (Position[i]==EMPTY) {
					 CreateCheckMove(*q, i);
				  } else break;
				}
		for (q+=(WHITEROOKS-WHITEBISHOPS), q+=*q; q!=Position+WHITEROOKS; q--) {
				for (i=*q+10; i<90 ; i+=10)
				  if (Position[i]==EMPTY) {
					  CreateCheckMove(*q, i);
				  } else break;
				for (i=*q-10; i>9 ; i-=10)
				  if (Position[i]==EMPTY) {
					  CreateCheckMove(*q, i);
				  } else break;
				for (i=*q+1; Valid[i] ; i++)
					 if (Position[i]==EMPTY) {
					  CreateCheckMove(*q, i);
				  } else break;
				for (i=*q-1; Valid[i] ; i--)
					  if (Position[i]==EMPTY) {
						CreateCheckMove(*q, i);
					  } else break;
		}
		for (q+=(WHITEQUEENS-WHITEROOKS), q+=*q; q!=Position+WHITEQUEENS; q--) {
				for (i=*q+10; i<90 ; i+=10)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q-10; i>9 ; i-=10)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q+1; Valid[i] ; i++)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q-1; Valid[i] ; i--)
								  if (Position[i]==EMPTY) {
									 CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q+11; Valid[i] ; i+=11)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q-11; Valid[i] ; i-=11)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q-9; Valid[i] ; i-=9)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q+9; Valid[i] ; i+=9)
								  if (Position[i]==EMPTY) {
									 CreateCheckMove(*q, i);
								  } else break;
		}
		q+=(WKINGPOSITION-WHITEQUEENS);
		SquarePointer=Position+*q;
		x=GetFile[*q];
		y=GetRank[*q];
		if (x>1 && *(SquarePointer-10)==EMPTY) CreateCheckMove(*q, *q-10);
		if (x<8 && *(SquarePointer+10)==EMPTY) CreateCheckMove(*q, *q+10);
		if (y>1 && *(SquarePointer-1)==EMPTY) CreateCheckMove(*q, *q-1);
		if (y<8 && *(SquarePointer+1)==EMPTY) CreateCheckMove(*q, *q+1);
		if (x>1 && y>1 && *(SquarePointer-11)==EMPTY) CreateCheckMove(*q, *q-11);
		if (x<8 && y<8 && *(SquarePointer+11)==EMPTY) CreateCheckMove(*q, *q+11);
		if (x>1 && y<8 && *(SquarePointer-9)==EMPTY) CreateCheckMove(*q, *q-9);
		if (x<8 && y>1 && *(SquarePointer+9)==EMPTY) CreateCheckMove(*q, *q+9);
	} else {
		POSITIONELEMENT* q=Position+BLACKPAWNS;
		for (q+=*q; q!=Position+BLACKPAWNS; q--) {
				SquarePointer=Position+*q;
				x=GetFile[*q];
				y=GetRank[*q];
				if (*(SquarePointer-1)==EMPTY) {
							  if (y==2)	{
									CreateCheckMovePromote(*q, *q-1, QUEEN);
							  } else {
									CreateCheckMove(*q, *q-1);
							  }
							  if (y==7 && *(SquarePointer-2)==EMPTY)
								  CreateCheckMove(*q, *q-2);
						  }
		}
		for (q+=(BLACKKNIGHTS-BLACKPAWNS), q+=*q; q!=Position+BLACKKNIGHTS; q--) {
				SquarePointer=Position+*q;
				x=GetFile[*q];
				y=GetRank[*q];
				if (x<8 && y>2 && *(SquarePointer+8)==EMPTY) CreateCheckMove(*q, *q+8);
				if (x>1 && y<7 && *(SquarePointer-8)==EMPTY) CreateCheckMove(*q, *q-8);
				if (x<8 && y<7 && *(SquarePointer+12)==EMPTY) CreateCheckMove(*q, *q+12);
				if (x>1 && y>2 && *(SquarePointer-12)==EMPTY) CreateCheckMove(*q, *q-12);
				if (x<7 && y>1 && *(SquarePointer+19)==EMPTY) CreateCheckMove(*q, *q+19);
				if (x>2 && y<8 && *(SquarePointer-19)==EMPTY) CreateCheckMove(*q, *q-19);
				if (x<7 && y<8 && *(SquarePointer+21)==EMPTY) CreateCheckMove(*q, *q+21);
				if (x>2 && y>1 && *(SquarePointer-21)==EMPTY) CreateCheckMove(*q, *q-21);
		}
		for (q+=(BLACKBISHOPS-BLACKKNIGHTS), q+=*q; q!=Position+BLACKBISHOPS; q--) {
				for (i=*q+11; Valid[i] ; i+=11)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q-11; Valid[i] ; i-=11)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q-9; Valid[i] ; i-=9)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q+9; Valid[i] ; i+=9)
								  if (Position[i]==EMPTY) {
									 CreateCheckMove(*q, i);
								  } else break;
		}
		for (q+=(BLACKROOKS-BLACKBISHOPS), q+=*q; q!=Position+BLACKROOKS; q--) {
				for (i=*q+10; i<90 ; i+=10)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q-10; i>9 ; i-=10)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q+1; Valid[i] ; i++)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q-1; Valid[i] ; i--)
								  if (Position[i]==EMPTY) {
									 CreateCheckMove(*q, i);
								  } else break;
		}
		for (q+=(BLACKQUEENS-BLACKROOKS), q+=*q; q!=Position+BLACKQUEENS; q--) {
				for (i=*q+10; i<90 ; i+=10)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q-10; i>9 ; i-=10)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q+1; Valid[i] ; i++)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q-1; Valid[i] ; i--)
								  if (Position[i]==EMPTY) {
									 CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q+11; Valid[i] ; i+=11)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q-11; Valid[i] ; i-=11)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q-9; Valid[i] ; i-=9)
								  if (Position[i]==EMPTY) {
									  CreateCheckMove(*q, i);
								  } else break;
						  for (i=*q+9; Valid[i] ; i+=9)
								  if (Position[i]==EMPTY) {
									 CreateCheckMove(*q, i);
								  } else break;
		}
		q+=(BKINGPOSITION-BLACKQUEENS);
		SquarePointer=Position+*q;
		x=GetFile[*q];
		y=GetRank[*q];
		if (x>1 && *(SquarePointer-10)==EMPTY) CreateCheckMove(*q, *q-10);
		if (x<8 && *(SquarePointer+10)==EMPTY) CreateCheckMove(*q, *q+10);
		if (y>1 && *(SquarePointer-1)==EMPTY) CreateCheckMove(*q, *q-1);
		if (y<8 && *(SquarePointer+1)==EMPTY) CreateCheckMove(*q, *q+1);
		if (x>1 && y>1 && *(SquarePointer-11)==EMPTY) CreateCheckMove(*q, *q-11);
		if (x<8 && y<8 && *(SquarePointer+11)==EMPTY) CreateCheckMove(*q, *q+11);
		if (x>1 && y<8 && *(SquarePointer-9)==EMPTY) CreateCheckMove(*q, *q-9);
		if (x<8 && y>1 && *(SquarePointer+9)==EMPTY) CreateCheckMove(*q, *q+9);
	}
		for (i=1; i<=Amount; i++) {
			if (MoveArray[i].From==PrincipalPath.Move[CurrentDepth].From &&
					MoveArray[i].To==PrincipalPath.Move[CurrentDepth].To)  {
					TMove TempMove=MoveArray[i];
					for (int j=i-1; j>=1; j--) {
						MoveArray[j+1]=MoveArray[j];
					}
					MoveArray[1]=TempMove;
			}
		}
#ifdef TESTING
	int t2 = GetTickCount() - t1;
	TotalGetCheckMoveListCalls++;
	TotalGetCheckMoveListMillis += t2;
#endif
	return Amount;
}


#define KINGDISTANCE 300
#define KINGKINGTROPISM 250
#define KINGPAWNTROPISM 250
#define TWOKNIGHTS 100
#define CORRECTBISHOPCORNER 2000
#define EDGEPAWN 250
#define ENEMYHASOPPOSITION 1500
#define PUSHPAWN 200

int TSearcher::LoneKing(TPosition Position)
{
	int WinningSide;
	int WinningKing;
	int LosingKing;
	int BishopColour=NOCOLOUR;
	int Score=
		Position[WHITEQUEENS]*QUEENVALUE+
		Position[WHITEBISHOPS]*BISHOPVALUE+
		Position[WHITEKNIGHTS]*KNIGHTVALUE+
		Position[WHITEROOKS]*ROOKVALUE+
		Position[WHITEPAWNS]*PAWNVALUE -
		Position[BLACKQUEENS]*QUEENVALUE -
		Position[BLACKBISHOPS]*BISHOPVALUE -
		Position[BLACKKNIGHTS]*KNIGHTVALUE -
		Position[BLACKROOKS]*ROOKVALUE -
		Position[BLACKPAWNS]*PAWNVALUE;

	if (Score==0) 
	{
		return 0;
	} 
	else if (Score>0) 
	{
		WinningSide=WHITE;
		WinningKing=Position[WKINGPOSITION];
		LosingKing=Position[BKINGPOSITION];
		if (Score==BISHOPVALUE && Position[WHITEBISHOPS]==1) return 0;
		if (Score==KNIGHTVALUE && Position[WHITEKNIGHTS]==1) return 0;
		if (Score==KNIGHTVALUE*2 && Position[WHITEKNIGHTS]==2) return TWOKNIGHTS;
		if (Score==KNIGHTVALUE+BISHOPVALUE &&
			Position[WHITEKNIGHTS]==1 &&
			Position[WHITEBISHOPS]==1) {
			BishopColour=(
				(GetX(Position[WHITEBISHOPS+1])+GetY(Position[WHITEBISHOPS+1]))%2==0
					? BLACK : WHITE);
		}
	} 
	else 
	{
		WinningSide=BLACK;
		WinningKing=Position[BKINGPOSITION];
		LosingKing=Position[WKINGPOSITION];
		Score=-Score;
		if (Score==BISHOPVALUE && Position[BLACKBISHOPS]==1) return 0;
		if (Score==KNIGHTVALUE && Position[BLACKKNIGHTS]==1) return 0;
		if (Score==KNIGHTVALUE*2 && Position[BLACKKNIGHTS]==2) return TWOKNIGHTS;
		if (Score==KNIGHTVALUE+BISHOPVALUE &&
			Position[BLACKKNIGHTS]==1 &&
			Position[BLACKBISHOPS]==1) {
			BishopColour=(
				(GetX(Position[BLACKBISHOPS+1])+GetY(Position[BLACKBISHOPS+1]))%2==0
					? BLACK : WHITE);
		}
	}

	// force enemy king to edge of board
	Score+=(int)((min(abs(GetX(LosingKing)-4.5), abs(GetY(LosingKing)-4.5))*KINGDISTANCE));
	//Score+=((abs(GetX(LosingKing)-4.5)+
	//			abs(GetY(LosingKing)-4.5))*
	//			KINGDISTANCE);

	// If needed, send enemy king to correct bishop corner
	if ((BishopColour==WHITE && Quadrant[LosingKing]%2==0) ||
		 (BishopColour==BLACK && Quadrant[LosingKing]%2==1)) {
			Score+=(int)(((abs(GetX(LosingKing)-4.5)+
						abs(GetY(LosingKing)-4.5))*
						KINGDISTANCE));
	}
	// send friendly king close to enemy king
	Score+=(int)((TropismNear[WinningKing][LosingKing]*KINGKINGTROPISM));

	Score/=(int)10.0;
	if (WinningSide==Position[MOVER])
	{
		return Score;
	}
	else
	{
		return -Score;
	}
};

void
TSearcher::SetUseCheckExtensions(int use)
{
	UseCheckExtensions=use;
}

void
TSearcher::SetUsePawnPushExtensions(int use)
{
	UsePawnPushExtensions=use;
}

void
TSearcher::SetNullMoveReduceDepth(int depth)
{
	NullMoveReduceDepth=depth;
}

void
TSearcher::SetMaxExtensions(int max)
{
	MaxExtensions=max;
}

void
TSearcher::SetAspireWindow(int window)
{
	AspireWindow=window;
}

void
TSearcher::SetNullMoveStopMaterial(int mat)
{
	NullMoveStopMaterial=mat;
}

void
TSearcher::SetHashReadReduce(int red)
{
	HashReadReduce=red;
}

void
TSearcher::SetHashWriteReduce(int red)
{
	HashWriteReduce=red;
}

void
TSearcher::SetPrintPV(int InPrintPV)
{
	PrintPV=InPrintPV;
}

void
TSearcher::SetUseSingleReplyExtensions(int use)
{
	UseSingleReplyExtensions=use;
}

void
TSearcher::SetStopScore(int Score) {
	StopScore=Score;
}

void
TSearcher::SetStopMove(TMove Move) {
	StopMove=Move;
}

void
TSearcher::SetRandomMoveOrder(int order) {
	RandomMoveOrder=order;
}

void
TSearcher::SetSearchMoves(string* searchMoves) {
}

void
TSearcher::SetPonderMode(int isPonder) {
}

void
TSearcher::SetWhiteMillisRemaining(int whiteMillisRemaining) {
}

void
TSearcher::SetBlackMillisRemaining(int blackMillisRemaining) {
}

void
TSearcher::SetWhiteIncrementMillis(int whiteIncrementMillis) {
}

void
TSearcher::SetBlackIncrementMillis(int blackIncrementMillis) {
}

void
TSearcher::SetMovesToGoToTimeControl(int movesToGoToTimeControl) {
}

void
TSearcher::SetMaxSearchNodes(int maxSearchNodes) {
}

void
TSearcher::SetisSearchingForMate(int isSearchForMate) {
}

void
TSearcher::SetMaxMoveTimeMillis(int timeToMoveMillis) {
}

void
TSearcher::SetSearchTimeMillis(int i) 
{
	searchTimeMillis = i;
}

void
TSearcher::SetMaxExtendedSearchTimeMillis(int i) 
{
	MaxExtendedSearchTimeMillis = i;
}

int
TSearcher::GetSearchStartTime() 
{
	return searchStartTime;
}

