#pragma unmanaged

#include "chessbrd.h"
#include "logger.h"

#include <string.h>
// _RTLDLL;_BIDSDLL;_OWLDLL;_OWLALLPCH;
#undef TESTING

//extern char OPENINGS[MAXFILENAMELENGTH];
int FENTimer;

TChessBoard::TChessBoard()
#ifdef USE_CLASSLIB
  : MovesMade(50, 1, 10),
	 WhiteClocks(50, 0, 10),
	 BlackClocks(50, 0, 10)
#endif
{
	 int StartPos[89];
	 OriginalPosition=TRUE;
	 StartPos[MOVER]=WHITE;
	 int i;
	 for (i=1; i<89; i++) StartPos[i]=EMPTY;
	 for (i=1; i<=10; i++) StartPos[i]=0;
	 for (i=12; i<=82; i+=10) StartPos[i]=WP;
	 for (i=17; i<=87; i+=10) StartPos[i]=BP;
	 StartPos[11]=WR; StartPos[18]=BR;
	 StartPos[21]=WN; StartPos[28]=BN;
	 StartPos[31]=WB; StartPos[38]=BB;
	 StartPos[41]=WQ; StartPos[48]=BQ;
	 StartPos[51]=WK; StartPos[58]=BK;
	 StartPos[61]=WB; StartPos[68]=BB;
	 StartPos[71]=WN; StartPos[78]=BN;
	 StartPos[81]=WR; StartPos[88]=BR;

	 for (i=0; i<89; i++)
		ResetTo[i]=StartPos[i];
	 Initialise();
}

TChessBoard::TChessBoard(int* SetupPosition)
#ifdef USE_CLASSLIB
  : MovesMade(50, 1, 10),
	 WhiteClocks(50, 0, 10),
	 BlackClocks(50, 0, 10)
#endif
{
	 int i;
	 OriginalPosition=FALSE;
	 for (i=0; i<89; i++)
		ResetTo[i]=SetupPosition[i];
	 Initialise();
}

TChessBoard::TChessBoard(char* Fen)
#ifdef USE_CLASSLIB
  : MovesMade(50, 1, 10),
	 WhiteClocks(50, 0, 10),
	 BlackClocks(50, 0, 10)
#endif
{
	 OriginalPosition=FALSE;

	 TranslateFenToBoard(Fen, ResetTo);

	 Initialise();
}

void
TChessBoard::Initialise()
{
	 ResetBoard();
	 MovesMade.Flush();
	 WhiteClocks.Flush();
	 BlackClocks.Flush();
	 MovePointer=0;
	 MovesStored=0;
	 WhiteClock=0;
	 BlackClock=0;
	 WhiteClocks.AddAt(0, 0);
	 BlackClocks.AddAt(0, 0);
	 GameSaved=TRUE;
	 DrawAgreed=FALSE;
	 Resigned=NOCOLOUR;
}

void
TChessBoard::SetWhiteClock(long MilliSeconds)
{
  WhiteClock=MilliSeconds;
}

void
TChessBoard::SetBlackClock(long MilliSeconds)
{
  BlackClock=MilliSeconds;
}

void
TChessBoard::SetWhiteStart(long MilliSeconds)
{
  WhiteClocks.SetData(0, MilliSeconds);
  WhiteClock=MilliSeconds;
}

void
TChessBoard::SetBlackStart(long MilliSeconds)
{
  BlackClocks.SetData(0, MilliSeconds);
  BlackClock=MilliSeconds;
}

long
TChessBoard::GetWhiteClock()
{
  return WhiteClock;
}

long
TChessBoard::GetBlackClock()
{
	return BlackClock;
}

long
TChessBoard::MakeStorable(TMove Move)
{
	long Result;
	Result=Move.Capture==EMPTY ? 0 : 100000L;
	Result+=(long)Move.PromotionPiece*(long)10000;
	Result+=(long)Move.From*(long)100;
	Result+=(long)Move.To;
	return Result;
}

int
TChessBoard::TotalMovesMade()
{
//  return MovesMade.GetItemsInContainer();
	return MovesStored;
}

int
TChessBoard::LastMoveMade()
{
  return MovePointer;
}

TMove
TChessBoard::GetLastMoveDetails()
{
  TMove RetMove;
  if (MovePointer>0)
	 RetMove=MovesMade[MovePointer]; else
	 RetMove.From=-1;
  return RetMove;
}

void
TChessBoard::AddMove(TMoveList& List, int Fx, int Fy, int Tx, int Ty)
{
	TMove m;
	int MeChecked;
	if (Fx<1 || Fx>8 || Tx<1 || Tx>8 || (Square[Tx*10+Ty]%100)==6)
	  exit(0);
	BackUpBoard(BACKUP);
	m.From=Fx*10+Fy;
	m.To=Tx*10+Ty;
	MakeMove(m, FALSE);
	if (Square[MOVER]==WHITE) Square[MOVER]=BLACK; else Square[MOVER]=WHITE; // Want to see check from point of view of non-Square[MOVER]
	MeChecked=IsCheck();
	if (!MeChecked) {
	  m.Capture=Square[m.To];
	  if (Square[MOVER]==WHITE) Square[MOVER]=BLACK; else Square[MOVER]=WHITE; // Want to see check from point of view of non-Square[MOVER]
	  List.Moves.Add(m);
	}
	BackUpBoard(RESTORE);
}

int
TChessBoard::GetMoveList(TMoveList& List)
{
	int x, y, i;
	int Mover;
	int Blocked;
	int SquareIndex;
	List.Moves.Flush();
	Mover=Square[MOVER];
	for (x=1; x<=8; x++)
	  for (y=1; y<=8; y++) {
		 SquareIndex=x*10+y;
		 switch (Square[SquareIndex]) {
			 case WP : if (Mover==BLACK) break;
						  if (Square[SquareIndex+1]==EMPTY) {
							 AddMove(List, x, y, x, y+1);
							 if (y==2 && Square[SquareIndex+2]==EMPTY) {
								AddMove(List, x, y, x, y+2);
							 }
						  }
						  if (x<8 && Square[SquareIndex+11]>EMPTY)
							 AddMove(List, x, y, x+1, y+1);
						  if (x>1 && Square[SquareIndex-9]>EMPTY)
							 AddMove(List, x, y, x-1, y+1);
						  if (y==5 && x>1 && x-1==Square[ENPAWN])
							 AddMove(List, x, y, x-1, y+1);
						  if (y==5 && x<8 && x+1==Square[ENPAWN])
							 AddMove(List, x, y, x+1, y+1);
						  break;
			 case BP : if (Mover==WHITE) break;
						  if (y>1 && Square[SquareIndex-1]==EMPTY) {
							 AddMove(List, x, y, x, y-1);
							 if (y==7 && Square[SquareIndex-2]==EMPTY) {
								AddMove(List, x, y, x, y-2);
							 }
						  }
						  if (x>1 && Square[SquareIndex-11]<EMPTY)
							 AddMove(List, x, y, x-1, y-1);
						  if (x<8 && Square[SquareIndex+9]<EMPTY)
							 AddMove(List, x, y, x+1, y-1);
						  if (y==4 && x>1 && x-1==Square[ENPAWN])
							 AddMove(List, x, y, x-1, y-1);
						  if (y==4 && x<8 && x+1==Square[ENPAWN])
							 AddMove(List, x, y, x+1, y-1);
						  break;
			 case WK : if (Mover==BLACK) break;
						  if (x>1 && Square[SquareIndex-10]>=EMPTY) AddMove(List, x, y, x-1, y);
						  if (x<8 && Square[SquareIndex+10]>=EMPTY) AddMove(List, x, y, x+1, y);
						  if (y>1 && Square[SquareIndex-1]>=EMPTY) AddMove(List, x, y, x, y-1);
						  if (y<8 && Square[SquareIndex+1]>=EMPTY) AddMove(List, x, y, x, y+1);
						  if (x>1 && y>1 && Square[SquareIndex-11]>=EMPTY) AddMove(List, x, y, x-1, y-1);
						  if (x<8 && y<8 && Square[SquareIndex+11]>=EMPTY) AddMove(List, x, y, x+1, y+1);
						  if (x>1 && y<8 && Square[SquareIndex-9]>=EMPTY) AddMove(List, x, y, x-1, y+1);
						  if (x<8 && y>1 && Square[SquareIndex+9]>=EMPTY) AddMove(List, x, y, x+1, y-1);
						  if (x==5 && y==1 && !Square[WKINGMOVED]) {
								 if (!IsCheck()) {
									if (!Square[WROOK8MOVED]) {
									  if (Square[61]==EMPTY && Square[71]==EMPTY) {
										  Square[61]=WK;
										  Square[51]=EMPTY;
										  int NoCheck=!IsCheck();
										  Square[51]=WK;
										  Square[61]=EMPTY;
										  if (NoCheck) {
											 if (Square[71]==EMPTY)
												AddMove(List, x, y, x+2, y);
										  }
									  }
									}
									if (!Square[WROOK1MOVED]) {
									  if (Square[41]==EMPTY && Square[31]==EMPTY && Square[21]==EMPTY) {
										  Square[41]=WK;
										  Square[51]=EMPTY;
										  int NoCheck=!IsCheck();
										  Square[51]=WK;
										  Square[41]=EMPTY;
										  if (NoCheck) {
											 if (Square[31]==EMPTY)
												AddMove(List, x, y, x-2, y);
										  }
									  }
									}
								 }
						  }
						  break;
			 case BK : if (Mover==WHITE) break;
						  if (x>1 && Square[SquareIndex-10]<=EMPTY) AddMove(List, x, y, x-1, y);
						  if (x<8 && Square[SquareIndex+10]<=EMPTY) AddMove(List, x, y, x+1, y);
						  if (y>1 && Square[SquareIndex-1]<=EMPTY)
							  AddMove(List, x, y, x, y-1);
						  if (y<8 && Square[SquareIndex+1]<=EMPTY) AddMove(List, x, y, x, y+1);
						  if (x>1 && y>1 && Square[SquareIndex-11]<=EMPTY) AddMove(List, x, y, x-1, y-1);
						  if (x<8 && y<8 && Square[SquareIndex+11]<=EMPTY) AddMove(List, x, y, x+1, y+1);
						  if (x>1 && y<8 && Square[SquareIndex-9]<=EMPTY) AddMove(List, x, y, x-1, y+1);
						  if (x<8 && y>1 && Square[SquareIndex+9]<=EMPTY) AddMove(List, x, y, x+1, y-1);
						  if (x==5 && y==8 && !Square[BKINGMOVED]) {
								 if (!IsCheck()) {
									if (!Square[BROOK8MOVED]) {
									  if (Square[68]==EMPTY && Square[78]==EMPTY) {
										  Square[68]=BK;
										  Square[58]=EMPTY;
										  int NoCheck=!IsCheck();
										  Square[58]=BK;
										  Square[68]=EMPTY;
										  if (NoCheck) {
											 if (Square[78]==EMPTY)
												AddMove(List, x, y, x+2, y);
										  }
									  }
									}
									if (!Square[BROOK1MOVED]) {
									  if (Square[48]==EMPTY && Square[38]==EMPTY && Square[28]==EMPTY) {
										  Square[48]=BK;
										  Square[58]=EMPTY;
										  int NoCheck=!IsCheck();
										  Square[58]=BK;
										  Square[48]=EMPTY;
										  if (NoCheck) {
											 if (Square[38]==EMPTY)
												AddMove(List, x, y, x-2, y);
										  }
									  }
									}
								 }
						  }
						  break;
			 case WN : if (Square[MOVER]==BLACK) break;
						  if (GetX(SquareIndex)<8 && GetY(SquareIndex)>2 && Square[SquareIndex+8]>=EMPTY) AddMove(List, x, y, x+1, y-2);
						  if (GetX(SquareIndex)>1 && GetY(SquareIndex)<7 && Square[SquareIndex-8]>=EMPTY) AddMove(List, x, y, x-1, y+2);
						  if (GetX(SquareIndex)<8 && GetY(SquareIndex)<7 && Square[SquareIndex+12]>=EMPTY) AddMove(List, x, y, x+1, y+2);
						  if (GetX(SquareIndex)>1 && GetY(SquareIndex)>2 && Square[SquareIndex-12]>=EMPTY) AddMove(List, x, y, x-1, y-2);
						  if (GetX(SquareIndex)<7 && GetY(SquareIndex)>1 && Square[SquareIndex+19]>=EMPTY) AddMove(List, x, y, x+2, y-1);
						  if (GetX(SquareIndex)>2 && GetY(SquareIndex)<8 && Square[SquareIndex-19]>=EMPTY) AddMove(List, x, y, x-2, y+1);
						  if (GetX(SquareIndex)<7 && GetY(SquareIndex)<8 && Square[SquareIndex+21]>=EMPTY) AddMove(List, x, y, x+2, y+1);
						  if (GetX(SquareIndex)>2 && GetY(SquareIndex)>1 && Square[SquareIndex-21]>=EMPTY) AddMove(List, x, y, x-2, y-1);
						  break;
			 case BN : if (Square[MOVER]==WHITE) break;
						  if (GetX(SquareIndex)<8 && GetY(SquareIndex)>2 && Square[SquareIndex+8]<=EMPTY) AddMove(List, x, y, x+1, y-2);
						  if (GetX(SquareIndex)>1 && GetY(SquareIndex)<7 && Square[SquareIndex-8]<=EMPTY) AddMove(List, x, y, x-1, y+2);
						  if (GetX(SquareIndex)<8 && GetY(SquareIndex)<7 && Square[SquareIndex+12]<=EMPTY) AddMove(List, x, y, x+1, y+2);
						  if (GetX(SquareIndex)>1 && GetY(SquareIndex)>2 && Square[SquareIndex-12]<=EMPTY) AddMove(List, x, y, x-1, y-2);
						  if (GetX(SquareIndex)<7 && GetY(SquareIndex)>1 && Square[SquareIndex+19]<=EMPTY) AddMove(List, x, y, x+2, y-1);
						  if (GetX(SquareIndex)>2 && GetY(SquareIndex)<8 && Square[SquareIndex-19]<=EMPTY) AddMove(List, x, y, x-2, y+1);
						  if (GetX(SquareIndex)<7 && GetY(SquareIndex)<8 && Square[SquareIndex+21]<=EMPTY) AddMove(List, x, y, x+2, y+1);
						  if (GetX(SquareIndex)>2 && GetY(SquareIndex)>1 && Square[SquareIndex-21]<=EMPTY) AddMove(List, x, y, x-2, y-1);
						  break;
			 case WR : if (Square[MOVER]==BLACK) break;
						  if (GetX(SquareIndex)<8)
							  for (Blocked=FALSE, i=SquareIndex+10; GetX(i)<=8 && !Blocked; i+=10)
								  if (Square[i]>=EMPTY) {
									  AddMove(List, x, y, GetX(i), y);
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)>1)
							  for (Blocked=FALSE, i=SquareIndex-10; GetX(i)>=1 && !Blocked; i-=10)
								  if (Square[i]>=EMPTY) {
									  AddMove(List, x, y, GetX(i), y);
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetY(SquareIndex)<8)
							  for (Blocked=FALSE, i=SquareIndex+1; GetY(i)<=8 && !Blocked; i++)
								  if (Square[i]>=EMPTY) {
									  AddMove(List, x, y, x, GetY(i));
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetY(SquareIndex)>1)
							  for (Blocked=FALSE, i=SquareIndex-1; GetY(i)>=1 && !Blocked; i--)
								  if (Square[i]>=EMPTY) {
									 AddMove(List, x, y, x, GetY(i));
									 if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  break;
			 case BR : if (Square[MOVER]==WHITE) break;
						  if (GetX(SquareIndex)<8)
							  for (Blocked=FALSE, i=SquareIndex+10; GetX(i)<=8 && !Blocked; i+=10)
								  if (Square[i]<=EMPTY) {
									  AddMove(List, x, y, GetX(i), y);
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)>1)
							  for (Blocked=FALSE, i=SquareIndex-10; GetX(i)>=1 && !Blocked; i-=10)
								  if (Square[i]<=EMPTY) {
									  AddMove(List, x, y, GetX(i), y);
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetY(SquareIndex)<8)
							  for (Blocked=FALSE, i=SquareIndex+1; GetY(i)<=8 && !Blocked; i++)
								  if (Square[i]<=EMPTY) {
									 AddMove(List, x, y, x, GetY(i));
									 if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetY(SquareIndex)>1)
							  for (Blocked=FALSE, i=SquareIndex-1; GetY(i)>=1 && !Blocked; i--)
								  if (Square[i]<=EMPTY) {
									 AddMove(List, x, y, x, GetY(i));
									 if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  break;
			 case WB : if (Square[MOVER]==BLACK) break;
						  if (GetX(SquareIndex)<8 && GetY(SquareIndex)<8)
							  for (Blocked=FALSE, i=SquareIndex+11; GetX(i)<=8 && GetY(i)<=8 && !Blocked; i+=11)
								  if (Square[i]>=EMPTY) {
									  AddMove(List, x, y, GetX(i), GetY(i));
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)>1 && GetY(SquareIndex)>1)
							  for (Blocked=FALSE, i=SquareIndex-11; GetX(i)>=1 && GetY(i)>=1 && !Blocked; i-=11)
								  if (Square[i]>=EMPTY) {
									  AddMove(List, x, y, GetX(i), GetY(i));
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)>1 && GetY(SquareIndex)<8)
							  for (Blocked=FALSE, i=SquareIndex-9; GetX(i)>=1 && GetY(i)<=8 && !Blocked; i-=9)
								  if (Square[i]>=EMPTY) {
									  AddMove(List, x, y, GetX(i), GetY(i));
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)<8 && GetY(SquareIndex)>1)
							  for (Blocked=FALSE, i=SquareIndex+9; GetX(i)<=8 && GetY(i)>=1 && !Blocked; i+=9)
								  if (Square[i]>=EMPTY) {
									 AddMove(List, x, y, GetX(i), GetY(i));
									 if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  break;
			 case BB : if (Square[MOVER]==WHITE) break;
						  if (GetX(SquareIndex)<8 && GetY(SquareIndex)<8)
							  for (Blocked=FALSE, i=SquareIndex+11; GetX(i)<=8 && GetY(i)<=8 && !Blocked; i+=11)
								  if (Square[i]<=EMPTY) {
									  AddMove(List, x, y, GetX(i), GetY(i));
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)>1 && GetY(SquareIndex)>1)
							  for (Blocked=FALSE, i=SquareIndex-11; GetX(i)>=1 && GetY(i)>=1 && !Blocked; i-=11)
								  if (Square[i]<=EMPTY) {
									  AddMove(List, x, y, GetX(i), GetY(i));
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)>1 && GetY(SquareIndex)<8)
							  for (Blocked=FALSE, i=SquareIndex-9; GetX(i)>=1 && GetY(i)<=8 && !Blocked; i-=9)
								  if (Square[i]<=EMPTY) {
									  AddMove(List, x, y, GetX(i), GetY(i));
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)<8 && GetY(SquareIndex)>1)
							  for (Blocked=FALSE, i=SquareIndex+9; GetX(i)<=8 && GetY(i)>=1 && !Blocked; i+=9)
								  if (Square[i]<=EMPTY) {
									 AddMove(List, x, y, GetX(i), GetY(i));
									 if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  break;
			 case WQ : if (Square[MOVER]==BLACK) break;
						  if (GetX(SquareIndex)<8)
							  for (Blocked=FALSE, i=SquareIndex+10; GetX(i)<=8 && !Blocked; i+=10)
								  if (Square[i]>=EMPTY) {
									  AddMove(List, x, y, GetX(i), y);
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)>1)
							  for (Blocked=FALSE, i=SquareIndex-10; GetX(i)>=1 && !Blocked; i-=10)
								  if (Square[i]>=EMPTY) {
									  AddMove(List, x, y, GetX(i), y);
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetY(SquareIndex)<8)
							  for (Blocked=FALSE, i=SquareIndex+1; GetY(i)<=8 && !Blocked; i++)
								  if (Square[i]>=EMPTY) {
									  AddMove(List, x, y, x, GetY(i));
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetY(SquareIndex)>1)
							  for (Blocked=FALSE, i=SquareIndex-1; GetY(i)>=1 && !Blocked; i--)
								  if (Square[i]>=EMPTY) {
									 AddMove(List, x, y, x, GetY(i));
									 if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)<8 && GetY(SquareIndex)<8)
							  for (Blocked=FALSE, i=SquareIndex+11; GetX(i)<=8 && GetY(i)<=8 && !Blocked; i+=11)
								  if (Square[i]>=EMPTY) {
									  AddMove(List, x, y, GetX(i), GetY(i));
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)>1 && GetY(SquareIndex)>1)
							  for (Blocked=FALSE, i=SquareIndex-11; GetX(i)>=1 && GetY(i)>=1 && !Blocked; i-=11)
								  if (Square[i]>=EMPTY) {
									  AddMove(List, x, y, GetX(i), GetY(i));
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)>1 && GetY(SquareIndex)<8)
							  for (Blocked=FALSE, i=SquareIndex-9; GetX(i)>=1 && GetY(i)<=8 && !Blocked; i-=9)
								  if (Square[i]>=EMPTY) {
									  AddMove(List, x, y, GetX(i), GetY(i));
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)<8 && GetY(SquareIndex)>1)
							  for (Blocked=FALSE, i=SquareIndex+9; GetX(i)<=8 && GetY(i)>=1 && !Blocked; i+=9)
								  if (Square[i]>=EMPTY) {
									 AddMove(List, x, y, GetX(i), GetY(i));
									 if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;

							break;
			 case BQ :  if (Square[MOVER]==WHITE) break;
							if (GetX(SquareIndex)<8)
							  for (Blocked=FALSE, i=SquareIndex+10; GetX(i)<=8 && !Blocked; i+=10)
								  if (Square[i]<=EMPTY) {
									  AddMove(List, x, y, GetX(i), y);
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)>1)
							  for (Blocked=FALSE, i=SquareIndex-10; GetX(i)>=1 && !Blocked; i-=10)
								  if (Square[i]<=EMPTY) {
									  AddMove(List, x, y, GetX(i), y);
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetY(SquareIndex)<8)
							  for (Blocked=FALSE, i=SquareIndex+1; GetY(i)<=8 && !Blocked; i++)
								  if (Square[i]<=EMPTY) {
									 AddMove(List, x, y, x, GetY(i));
									 if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetY(SquareIndex)>1)
							  for (Blocked=FALSE, i=SquareIndex-1; GetY(i)>=1 && !Blocked; i--)
								  if (Square[i]<=EMPTY) {
									 AddMove(List, x, y, x, GetY(i));
									 if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)<8 && GetY(SquareIndex)<8)
							  for (Blocked=FALSE, i=SquareIndex+11; GetX(i)<=8 && GetY(i)<=8 && !Blocked; i+=11)
								  if (Square[i]<=EMPTY) {
									  AddMove(List, x, y, GetX(i), GetY(i));
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)>1 && GetY(SquareIndex)>1)
							  for (Blocked=FALSE, i=SquareIndex-11; GetX(i)>=1 && GetY(i)>=1 && !Blocked; i-=11)
								  if (Square[i]<=EMPTY) {
									  AddMove(List, x, y, GetX(i), GetY(i));
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)>1 && GetY(SquareIndex)<8)
							  for (Blocked=FALSE, i=SquareIndex-9; GetX(i)>=1 && GetY(i)<=8 && !Blocked; i-=9)
								  if (Square[i]<=EMPTY) {
									  AddMove(List, x, y, GetX(i), GetY(i));
									  if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  if (GetX(SquareIndex)<8 && GetY(SquareIndex)>1)
							  for (Blocked=FALSE, i=SquareIndex+9; GetX(i)<=8 && GetY(i)>=1 && !Blocked; i+=9)
								  if (Square[i]<=EMPTY) {
									 AddMove(List, x, y, GetX(i), GetY(i));
									 if (Square[i]!=EMPTY) Blocked=TRUE;
								  } else Blocked=TRUE;
						  break;
		 }
	}
	List.Amount=List.Moves.GetItemsInContainer();
	return List.Amount;
}

int
TChessBoard::ThirdRepetition()
{
  int i;
  int reps=0;
  BackUpBoard(BACKUP);
  ResetBoard();
// First check initial position against current position
  if (BackUpSquare[MOVER]==Square[MOVER] && memcmp((const void *)&BackUpSquare[11], (const void *)&Square[11], 78*sizeof(int))==0)
		 reps++;
  for (i=1; i<=MovePointer; i++) {
	  MakeMove(MovesMade[i], FALSE);
	  if (BackUpSquare[MOVER]==Square[MOVER] && memcmp((const void *)&BackUpSquare[11], (const void *)&Square[11], 78*sizeof(int))==0)
		 reps++;
  }
  BackUpBoard(RESTORE);
  if (reps==3) return TRUE;
  return FALSE;
}

int
TChessBoard::GameStatus()
{
  int legal;
  TMoveList List;
  if (Resigned!=NOCOLOUR) return 11;
  if (DrawAgreed) return 12;
  if (ThirdRepetition()) return 4;
  legal=(GetMoveList(List)!=0);
  if (!legal) {
	  if (IsCheck()) {
		  return 1+(Square[MOVER]==WHITE);
	  } else
	  return 3;
  } else {
	  if (Square[FIFTYMOVES]>=100) {
			return 5;
	  }
  }
  return 0;
}

void
TChessBoard::ResetBoard()
{
  int i;
  for (i=0; i<89; i++)
	 Square[i]=ResetTo[i];
}

int
TChessBoard::GetMover()
{
	return(Square[MOVER]);
}

TMove
TChessBoard::GetMove(int number)
{
	return(MovesMade[number]);
}

int
TChessBoard::GetSquare(int i)
{
	return (Square[i]);
}

int
TChessBoard::IsCheck()
{
	int i;
	int KingSquare;
	int Block;
	if (Square[MOVER]==WHITE)
	{
		for (i=11, KingSquare=0; i<=88; i++)
			if (Square[i]==WK) KingSquare=i;
		if (KingSquare<11 || KingSquare>88) {
			exit(0);
		}
// Attacking Black Knight?
		if (GetX(KingSquare)>2 && GetY(KingSquare)>1 && Square[KingSquare-21]==BN) return TRUE;
		if (GetX(KingSquare)>2 && GetY(KingSquare)<8 && Square[KingSquare-19]==BN) return TRUE;
		if (GetX(KingSquare)>1 && GetY(KingSquare)>2 && Square[KingSquare-12]==BN) return TRUE;
		if (GetX(KingSquare)>1 && GetY(KingSquare)<7 && Square[KingSquare-8]==BN) return TRUE;
		if (GetX(KingSquare)<7 && GetY(KingSquare)<8 && Square[KingSquare+21]==BN) return TRUE;
		if (GetX(KingSquare)<7 && GetY(KingSquare)>1 && Square[KingSquare+19]==BN) return TRUE;
		if (GetX(KingSquare)<8 && GetY(KingSquare)<7 && Square[KingSquare+12]==BN) return TRUE;
		if (GetX(KingSquare)<8 && GetY(KingSquare)>2 && Square[KingSquare+8]==BN) return TRUE;
// Attacking Black Pawn?
		if (KingSquare>=11+9 && Square[KingSquare-9]==BP) return TRUE;
		if (KingSquare<=88-11 && Square[KingSquare+11]==BP) return TRUE;
// Attacking Black Rook or Queen?
		for (Block=FALSE, i=KingSquare+1; !Block && GetY(i)<=8; i++) if (Square[i]!=EMPTY) if (Square[i]==BQ || Square[i]==BR) return TRUE; else Block=TRUE;
		for (Block=FALSE, i=KingSquare-1; !Block && GetY(i)>=1; i--) if (Square[i]!=EMPTY) if (Square[i]==BQ || Square[i]==BR) return TRUE; else Block=TRUE;
		for (Block=FALSE, i=KingSquare+10; !Block && GetX(i)<=8; i+=10) if (Square[i]!=EMPTY) if (Square[i]==BQ || Square[i]==BR) return TRUE; else Block=TRUE;
		for (Block=FALSE, i=KingSquare-10; !Block && GetX(i)>=1; i-=10) if (Square[i]!=EMPTY) if (Square[i]==BQ || Square[i]==BR) return TRUE; else Block=TRUE;
// Attacking Black Bishop or Queen?
		for (Block=FALSE, i=KingSquare+11; !Block && GetX(i)<=8 && GetY(i)<=8; i+=11) if (Square[i]!=EMPTY) if (Square[i]==BQ || Square[i]==BB) return TRUE; else Block=TRUE;
		for (Block=FALSE, i=KingSquare-11; !Block && GetX(i)>=1 && GetY(i)>=1; i-=11) if (Square[i]!=EMPTY) if (Square[i]==BQ || Square[i]==BB) return TRUE; else Block=TRUE;
		for (Block=FALSE, i=KingSquare+9; !Block && GetX(i)<=8 && GetY(i)>=1; i+=9) if (Square[i]!=EMPTY) if (Square[i]==BQ || Square[i]==BB) return TRUE; else Block=TRUE;
		for (Block=FALSE, i=KingSquare-9; !Block && GetX(i)>=1 && GetY(i)<=8; i-=9) if (Square[i]!=EMPTY) if (Square[i]==BQ || Square[i]==BB) return TRUE; else Block=TRUE;
// Attacking Black King
		if (GetX(KingSquare)>1 && GetY(KingSquare)>1 && Square[KingSquare-11]==BK) return TRUE;
		if (GetX(KingSquare)>1 && GetY(KingSquare)<8 && Square[KingSquare-9]==BK) return TRUE;
		if (GetX(KingSquare)<8 && GetY(KingSquare)>1 && Square[KingSquare+9]==BK) return TRUE;
		if (GetX(KingSquare)<8 && GetY(KingSquare)<8 && Square[KingSquare+11]==BK) return TRUE;
		if (GetX(KingSquare)>1 && Square[KingSquare-10]==BK) return TRUE;
		if (GetY(KingSquare)>1 && Square[KingSquare-1]==BK) return TRUE;
		if (GetX(KingSquare)<8 && Square[KingSquare+10]==BK) return TRUE;
		if (GetY(KingSquare)<8 && Square[KingSquare+1]==BK) return TRUE;
	}
	if (Square[MOVER]==BLACK)
	{
		for (i=11, KingSquare=0; i<=88; i++)
			if (Square[i]==BK) KingSquare=i;
		if (KingSquare<11 || KingSquare>88) {
			exit(0);
		}
// Attacking White Knight?
		if (GetX(KingSquare)>2 && GetY(KingSquare)>1 && Square[KingSquare-21]==WN) return TRUE;
		if (GetX(KingSquare)>2 && GetY(KingSquare)<8 && Square[KingSquare-19]==WN) return TRUE;
		if (GetX(KingSquare)>1 && GetY(KingSquare)>2 && Square[KingSquare-12]==WN) return TRUE;
		if (GetX(KingSquare)>1 && GetY(KingSquare)<7 && Square[KingSquare-8]==WN) return TRUE;
		if (GetX(KingSquare)<7 && GetY(KingSquare)<8 && Square[KingSquare+21]==WN) return TRUE;
		if (GetX(KingSquare)<7 && GetY(KingSquare)>1 && Square[KingSquare+19]==WN) return TRUE;
		if (GetX(KingSquare)<8 && GetY(KingSquare)<7 && Square[KingSquare+12]==WN) return TRUE;
		if (GetX(KingSquare)<8 && GetY(KingSquare)>2 && Square[KingSquare+8]==WN) return TRUE;
// Attacking White Pawn?
		if (KingSquare<=88-9 && Square[KingSquare+9]==WP) return TRUE;
		if (KingSquare>=11+11 && Square[KingSquare-11]==WP) return TRUE;
// Attacking White Rook or Queen?
		for (Block=FALSE, i=KingSquare+1; !Block && GetY(i)<=8; i++) if (Square[i]!=EMPTY) if (Square[i]==WQ || Square[i]==WR) return TRUE; else Block=TRUE;
		for (Block=FALSE, i=KingSquare-1; !Block && GetY(i)>=1; i--) if (Square[i]!=EMPTY) if (Square[i]==WQ || Square[i]==WR) return TRUE; else Block=TRUE;
		for (Block=FALSE, i=KingSquare+10; !Block && GetX(i)<=8; i+=10) if (Square[i]!=EMPTY) if (Square[i]==WQ || Square[i]==WR) return TRUE; else Block=TRUE;
		for (Block=FALSE, i=KingSquare-10; !Block && GetX(i)>=1; i-=10) if (Square[i]!=EMPTY) if (Square[i]==WQ || Square[i]==WR) return TRUE; else Block=TRUE;
// Attacking White Bishop or Queen?
		for (Block=FALSE, i=KingSquare+11; !Block && GetX(i)<=8 && GetY(i)<=8; i+=11) if (Square[i]!=EMPTY) if (Square[i]==WQ || Square[i]==WB) return TRUE; else Block=TRUE;
		for (Block=FALSE, i=KingSquare-11; !Block && GetX(i)>=1 && GetY(i)>=1; i-=11) if (Square[i]!=EMPTY) if (Square[i]==WQ || Square[i]==WB) return TRUE; else Block=TRUE;
		for (Block=FALSE, i=KingSquare+9; !Block && GetX(i)<=8 && GetY(i)>=1; i+=9) if (Square[i]!=EMPTY) if (Square[i]==WQ || Square[i]==WB) return TRUE; else Block=TRUE;
		for (Block=FALSE, i=KingSquare-9; !Block && GetX(i)>=1 && GetY(i)<=8; i-=9) if (Square[i]!=EMPTY) if (Square[i]==WQ || Square[i]==WB) return TRUE; else Block=TRUE;
// Attacking White King
		if (GetX(KingSquare)>1 && GetY(KingSquare)>1 && Square[KingSquare-11]==WK) return TRUE;
		if (GetX(KingSquare)>1 && GetY(KingSquare)<8 && Square[KingSquare-9]==WK) return TRUE;
		if (GetX(KingSquare)<8 && GetY(KingSquare)>1 && Square[KingSquare+9]==WK) return TRUE;
		if (GetX(KingSquare)<8 && GetY(KingSquare)<8 && Square[KingSquare+11]==WK) return TRUE;
		if (GetX(KingSquare)>1 && Square[KingSquare-10]==WK) return TRUE;
		if (GetY(KingSquare)>1 && Square[KingSquare-1]==WK) return TRUE;
		if (GetX(KingSquare)<8 && Square[KingSquare+10]==WK) return TRUE;
		if (GetY(KingSquare)<8 && Square[KingSquare+1]==WK) return TRUE;
	}
	return FALSE;
}

void
TChessBoard::BackUpBoard(int direction)
{
		if (direction==BACKUP)
			memcpy(BackUpSquare, Square, sizeof(int)*89); else
			memcpy(Square, BackUpSquare, sizeof(int)*89);
}

void
TChessBoard::MakeMove(TMove Move, int Store)
{
	// This function makes the move 'Move' adjusting relevant flags
	// such as En-Passant and Castling flags.  It also adds the Move
	// to the class's private array of Moves Made.
	// It is the caller's responsibility to Verify that
	// the move is legal if verification is required.
	// The PromotionPiece variable holds the value of the piece that
	// a pawn will promote to if a pawn promotion move is made.
	// If none is specified, the Pawn will promote to a Queen.
	int From, To;
	From=Move.From;
	To=Move.To;
	Move.Capture=Square[To];
	Square[To]=Square[From];

	if (Move.Capture==EMPTY && Square[From]!=WP && Square[From]!=BP) {
		Square[FIFTYMOVES]++;
	} else {
		Square[FIFTYMOVES]=0;
	}

// Pawn Promotion?

	if (Square[To]==WP && GetY(To)==8)
		Square[To]=Move.PromotionPiece;

	if (Square[To]==BP && GetY(To)==1)
		Square[To]=Move.PromotionPiece+100;

	Square[From]=EMPTY;

	if (GetX(To)==Square[ENPAWN] && Square[To]==BP && GetY(To)==3)
	  { Square[To+1]=EMPTY; Move.Capture=WP; }
	if (GetX(To)==Square[ENPAWN] && Square[To]==WP && GetY(To)==6)
	  { Square[To-1]=EMPTY; Move.Capture=BP; }

	if (From==51 && To==71 && Square[To]==WK) {
		Square[61]=WR;	Square[81]=EMPTY;
		Square[WROOK8MOVED]=TRUE;
	}
	if (From==51 && To==31 && Square[To]==WK) {
		Square[41]=WR;	Square[11]=EMPTY;
		Square[WROOK1MOVED]=TRUE;
	}
	if (From==58 && To==78 && Square[To]==BK) {
		Square[68]=BR;	Square[88]=EMPTY;
		Square[BROOK8MOVED]=TRUE;
	}
	if (From==58 && To==38 && Square[To]==BK) {
		Square[48]=BR;	Square[18]=EMPTY;
		Square[BROOK1MOVED]=TRUE;
	}

	if (Square[MOVER]==WHITE) Square[MOVER]=BLACK;
		else Square[MOVER]=WHITE;
	if (From==51 || To==51) Square[WKINGMOVED]=TRUE;
	if (From==58 || To==58) Square[BKINGMOVED]=TRUE;
	if (From==11 || To==11) Square[WROOK1MOVED]=TRUE; // Even if it wasn't this move
	if (From==81 || To==81) Square[WROOK8MOVED]=TRUE;
	if (From==18 || To==18) Square[BROOK1MOVED]=TRUE;
	if (From==88 || To==88) Square[BROOK8MOVED]=TRUE;
	Square[ENPAWN]=0;
	if (Square[To]==WP && GetY(From)==2 && GetY(To)==4)
		Square[ENPAWN]=GetX(To);
	if (Square[To]==BP && GetY(From)==7 && GetY(To)==5)
		Square[ENPAWN]=GetX(To);

	if (Square[To]%100==PAWN)
		 Move.Score=TRUE; else
			Move.Score=FALSE;

	if (Store)
	{
	  MovePointer++;
	  MovesMade.AddAt(Move, MovePointer);
	  MovesStored=MovePointer;
	  WhiteClocks.AddAt(WhiteClock, MovePointer);
	  BlackClocks.AddAt(BlackClock, MovePointer);
	  GameSaved=FALSE;
	  Resigned=NOCOLOUR;
     DrawAgreed=FALSE;
	}
}

void
TChessBoard::TakeBackMove()
{
  int i;
  if (MovePointer==0) return;
  MovePointer--;
  ResetBoard();
  for (i=1; i<=MovePointer; i++)
	  MakeMove(MovesMade[i], FALSE);
  WhiteClock=WhiteClocks[MovePointer];
  BlackClock=BlackClocks[MovePointer];
}

void
TChessBoard::ReplayMove()
{
  int i;
  if (MovePointer>=/*MovesMade.GetItemsInContainer()*/MovesStored) return;
  MovePointer++;
  ResetBoard();
  for (i=1; i<=MovePointer; i++)
	  MakeMove(MovesMade[i], FALSE);
  WhiteClock=WhiteClocks[MovePointer];
  BlackClock=BlackClocks[MovePointer];
}

void
TChessBoard::TakeBackAllMoves()
{
  ResetBoard();
  MovePointer=0;
  WhiteClock=WhiteClocks[MovePointer];
  BlackClock=BlackClocks[MovePointer];
}

void
TChessBoard::ReplayAllMoves()
{
  int i;
  MovePointer=MovesStored;
  ResetBoard();
  for (i=1; i<=MovePointer; i++)
	  MakeMove(MovesMade[i], FALSE);
  WhiteClock=WhiteClocks[MovePointer];
  BlackClock=BlackClocks[MovePointer];
}

int
TChessBoard::VerifyMove(TMove Move)
{
	// The purpose is to determine whether the move is legal or not
	// by verifying correct movement of the piece and whether the
	// resulting position leaves the mover in check.
	int i, Piece, diff;
	int From, To;
	int Checked;
	TMoveList List;
	From=Move.From;
	To=Move.To;
	if (From/10<1 || From/10>8 || From%10<1 || From%10>8) return 299;
	if (To/10<1 || To/10>8 || To%10<1 || To%10>8) return 300;
	Piece=Square[From];
	if (From==To) return 301;
	if (Piece<EMPTY && Square[MOVER]==BLACK) return 302;
	if (Piece>EMPTY && Square[MOVER]==WHITE) return 303;
	if (Piece==EMPTY) return 304;
	if (Square[MOVER]==WHITE && Square[To]<EMPTY) return 305;
	if (Square[MOVER]==BLACK && Square[To]>EMPTY) return 306;
	switch(Piece)
	{
	  case WK : if ((abs(GetX(To)-GetX(From))>1 || abs(GetY(To)-GetY(From))>1) && !(From==51 && (To==71 || To==31))) return 1;
					if (From==51 && To==71)
					{
					  if (Square[61]!=EMPTY || Square[71]!=EMPTY) return 13;
					  if (Square[WROOK8MOVED]==TRUE) return 3;
					  if (Square[WKINGMOVED]==TRUE) return 4;
					  if (IsCheck()) return 22;
					  Square[61]=WK; Square[51]=EMPTY;
					  if (IsCheck()) {
						 Square[51]=WK; Square[61]=EMPTY;
						 return 21;
					  }
					  Square[51]=WK; Square[61]=EMPTY;
					}
					if (From==51 && To==31)
					{
					  if (Square[41]!=EMPTY || Square[31]!=EMPTY || Square[21]!=EMPTY) return 13;
					  if (Square[WROOK1MOVED]==TRUE) return 3;
					  if (Square[WKINGMOVED]==TRUE) return 4;
					  if (IsCheck()) return 22;
					  Square[41]=WK; Square[51]=EMPTY;
					  if (IsCheck()) {
						 Square[51]=WK; Square[41]=EMPTY;
						 return 21;
					  }
					  Square[51]=WK; Square[41]=EMPTY;
					}
					break;
	  case BK : if ((abs(GetX(To)-GetX(From))>1 || abs(GetY(To)-GetY(From))>1) && !(From==58 && (To==78 || To==38))) return 1;
					if (From==58 && To==78)
					{
					  if (Square[68]!=EMPTY || Square[78]!=EMPTY) return 13;
					  if (Square[BROOK8MOVED]==TRUE) return 3;
					  if (Square[BKINGMOVED]==TRUE) return 4;
					  if (IsCheck()) return 22;
					  Square[68]=BK; Square[58]=EMPTY;
					  if (IsCheck()) {
						 Square[58]=BK; Square[68]=EMPTY;
						 return 21;
					  }
					  Square[58]=BK; Square[68]=EMPTY;
					}
					if (From==58 && To==38)
					{
					  if (Square[48]!=EMPTY || Square[38]!=EMPTY || Square[28]!=EMPTY) return 13;
					  if (Square[BROOK1MOVED]==TRUE) return 3;
					  if (Square[BKINGMOVED]==TRUE) return 4;
					  if (IsCheck()) return 22;
					  Square[48]=BK; Square[58]=EMPTY;
					  if (IsCheck()) {
						 Square[58]=BK; Square[48]=EMPTY;
						 return 21;
					  }
					  Square[58]=BK; Square[48]=EMPTY;
					}
					break;
	  case WR : if (GetX(From)!=GetX(To) && GetY(From)!=GetY(To)) return 6;
					if (GetX(From)==GetX(To)) {
					  if (GetY(To)>GetY(From)) {
						  for (i=From+1; i<=To; i++) if (Square[i]<10) return 14; else if (Square[i]>100 && i!=To) return 14;
					  } else {
						  for (i=From-1; i>=To; i--) if (Square[i]<10) return 14; else if (Square[i]>100 && i!=To) return 14;
					  }
					} else {
					  if (GetX(To)>GetX(From)) {
						  for (i=From+10; i<=To; i+=10) if (Square[i]<10) return 14; else if (Square[i]>100 && i!=To) return 14;
					  } else {
						  for (i=From-10; i>=To; i-=10) if (Square[i]<10) return 14; else if (Square[i]>100 && i!=To) return 14;
					  }
					}
					break;
	  case BR : if (GetX(From)!=GetX(To) && GetY(From)!=GetY(To)) return 6;
					if (GetX(From)==GetX(To)) {
					  if (GetY(To)>GetY(From)) {
						  for (i=From+1; i<=To; i++) if (Square[i]>100) return 14; else if (Square[i]<10 && i!=To) return 14;
					  } else {
						  for (i=From-1; i>=To; i--) if (Square[i]>100) return 14; else if (Square[i]<10 && i!=To) return 14;
					  }
					} else {
					  if (GetX(To)>GetX(From)) {
						  for (i=From+10; i<=To; i+=10) if (Square[i]>100) return 14; else if (Square[i]<10 && i!=To) return 14;
					  } else {
						  for (i=From-10; i>=To; i-=10) if (Square[i]>100) return 14; else if (Square[i]<10 && i!=To) return 14;
					  }
					}
					break;
	  case WQ : if (!
						  (
							(From>To && (From-To)%9==0 && GetY(To)>GetY(From)) ||
							(From>To && (From-To)%11==0 && GetY(From)>GetY(To)) ||
							(To>From && (To-From)%11==0 && GetY(To)>GetY(From)) ||
							(To>From && (To-From)%9==0 && GetY(From)>GetY(To)) ||
							(GetX(From)==GetX(To)) ||
							(GetY(From)==GetY(To))
						  )
	  					) return 7;
					if (GetX(From)==GetX(To) && To>From) for (i=From+1; i<=To; i++) if (Square[i]<10 || (Square[i]>100 && i!=To)) return 20;
					if (GetX(From)==GetX(To) && From>To) for (i=From-1; i>=To; i--) if (Square[i]<10 || (Square[i]>100 && i!=To)) return 20;
					if (GetY(From)==GetY(To) && To>From) for (i=From+10; i<=To; i+=10) if (Square[i]<10 || (Square[i]>100 && i!=To)) return 20;
					if (GetY(From)==GetY(To) && From>To) for (i=From-10; i>=To; i-=10) if (Square[i]<10 || (Square[i]>100 && i!=To)) return 20;
					if (From>To && (From-To)%11==0) for (i=From-11; i>=To; i-=11) if (Square[i]<10 || (Square[i]>100 && i!=To)) return 20;
					if (To>From && (To-From)%11==0) for (i=From+11; i<=To; i+=11) if (Square[i]<10 || (Square[i]>100 && i!=To)) return 20;
					if (From>To && (From-To)%9==0) for (i=From-9; i>=To; i-=9) if (Square[i]<10 || (Square[i]>100 && i!=To)) return 20;
					if (To>From && (To-From)%9==0) for (i=From+9; i<=To; i+=9) if (Square[i]<10 || (Square[i]>100 && i!=To)) return 20;
					break;
	  case BQ : if (!
						  (
							(From>To && (From-To)%9==0 && GetY(To)>GetY(From)) ||
							(From>To && (From-To)%11==0 && GetY(From)>GetY(To)) ||
							(To>From && (To-From)%11==0 && GetY(To)>GetY(From)) ||
							(To>From && (To-From)%9==0 && GetY(From)>GetY(To)) ||
							(GetX(From)==GetX(To)) ||
							(GetY(From)==GetY(To))
						  )
	  					) return 7;
					if (GetX(From)==GetX(To) && To>From) for (i=From+1; i<=To; i++) if (Square[i]>100 || (Square[i]<10 && i!=To)) return 20;
					if (GetX(From)==GetX(To) && From>To) for (i=From-1; i>=To; i--) if (Square[i]>100 || (Square[i]<10 && i!=To)) return 20;
					if (GetY(From)==GetY(To) && To>From) for (i=From+10; i<=To; i+=10) if (Square[i]>100 || (Square[i]<10 && i!=To)) return 20;
					if (GetY(From)==GetY(To) && From>To) for (i=From-10; i>=To; i-=10) if (Square[i]>100 || (Square[i]<10 && i!=To)) return 20;
					if (From>To && (From-To)%11==0) for (i=From-11; i>=To; i-=11) if (Square[i]>100 || (Square[i]<10 && i!=To)) return 20;
					if (To>From && (To-From)%11==0) for (i=From+11; i<=To; i+=11) if (Square[i]>100 || (Square[i]<10 && i!=To)) return 20;
					if (From>To && (From-To)%9==0) for (i=From-9; i>=To; i-=9) if (Square[i]>100 || (Square[i]<10 && i!=To)) return 20;
					if (To>From && (To-From)%9==0) for (i=From+9; i<=To; i+=9) if (Square[i]>100 || (Square[i]<10 && i!=To)) return 20;
					break;
	  case WP : if (GetY(From)>GetY(To)) return 16; // moving backwards?
					// attempting capture?
					if (Square[To]>100)
					  if (To-From!=11 && From-To!=9) return 9; else break;
					// attempting 2 squares?
					if (GetY(To)-GetY(From)==2 && (GetX(To)==GetX(From))) {
						if (GetY(From)!=2) return 10; // not on correct rank
							else if (Square[From+1]!=EMPTY) return 17; // attempted jump
								else break;
					}
					// attempting to move diagonally (if for capture, would not get this far)
					if (GetX(From)!=GetX(To)) {
						 if (To-From==11 || From-To==9) { // No enemy, en-passant perhaps?
								 if (GetX(To)==Square[ENPAWN] && GetY(To)==6) break;
									else return 18;
						 } else
						 return 8;
					} else {  // must now be going straight forward, no capturing and no 2-square attempt
						if (GetY(To)-GetY(From)>1) return 8; else
							if (Square[To]>100) return 11; else // can't capture like this
								break;
					}
	  case BP : if (GetY(From)<GetY(To)) return 16;  // moving backwards?
					// attempting capture?
					if (Square[To]<10)
					  if (From-To!=11 && To-From!=9) return 9; else break;
					// attempting 2 squares?
					if (GetY(From)-GetY(To)==2 && (GetX(To)==GetX(From))) {
						if (GetY(From)!=7) return 10; // not on correct rank
							else if (Square[From-1]!=EMPTY) return 17; // attempted jump
								else break;
					}
					// attempting to move diagonally (if for capture, would not get this far)
					if (GetX(From)!=GetX(To)) {
						 if (From-To==11 || To-From==9) { // No enemy, en-passant perhaps?
								 if (GetX(To)==Square[ENPAWN] && GetY(To)==3) break;
									else return 18;
						 } else
						 return 8;
					} else {  // must now be going straight forward, no capturing and no 2-square attempt
						if (GetY(From)-GetY(To)>1) return 8; else
							if (Square[To]<10) return 11; else // can't capture like this
								break;
					}
	  case WB : if ((To>From) && GetY(To)>GetY(From)) { // North-East
					  if (abs(From-To)%11!=0) return 12;
					  for (i=From+11; i<=To; i+=11) if (Square[i]<10) return 15; else if (Square[i]>100 && i!=To) return 15;
					} else
					if ((To>From) && GetY(To)<GetY(From)) { // South-East
					  if (abs(From-To)%9!=0) return 12;
					  for (i=From+9; i<=To; i+=9) if (Square[i]<10) return 15; else if (Square[i]>100 && i!=To) return 15;
					} else
					if ((To<From) && GetY(To)>GetY(From)) { // North-West
					  if (abs(From-To)%9!=0) return 12;
					  for (i=From-9; i>=To; i-=9) if (Square[i]<10) return 15; else if (Square[i]>100 && i!=To) return 15;
					} else
					if ((To<From) && GetY(To)<GetY(From)) { // South-West
					  if (abs(From-To)%11!=0) return 12;
					  for (i=From-11; i>=To; i-=11) if (Square[i]<10) return 15; else if (Square[i]>100 && i!=To) return 15;
					} else return 12;
					break;
	  case BB : if ((To>From) && GetY(To)>GetY(From)) { // North-East
					  if (abs(From-To)%11!=0) return 12;
					  for (i=From+11; i<=To; i+=11) if (Square[i]>100) return 15; else if (Square[i]<10 && i!=To) return 15;
					} else
					if ((To>From) && GetY(To)<GetY(From)) { // South-East
					  if (abs(From-To)%9!=0) return 12;
					  for (i=From+9; i<=To; i+=9) if (Square[i]>100) return 15; else if (Square[i]<10 && i!=To) return 15;
					} else
					if ((To<From) && GetY(To)>GetY(From)) { // North-West
					  if (abs(From-To)%9!=0) return 12;
					  for (i=From-9; i>=To; i-=9) if (Square[i]>100) return 15; else if (Square[i]<10 && i!=To) return 15;
					} else
					if ((To<From) && GetY(To)<GetY(From)) { // South-West
					  if (abs(From-To)%11!=0) return 12;
					  for (i=From-11; i>=To; i-=11) if (Square[i]>100) return 15; else if (Square[i]<10 && i!=To) return 15;
					} else return 12;
					break;
	  case WN : diff=abs(From-To);
					if (diff!=12 && diff!=8 && diff!=21 && diff!=19) return 5;
					break;
	  case BN : diff=abs(From-To);
					if (diff!=12 && diff!=8 && diff!=21 && diff!=19) return 5;
					break;
	}
// Is the mover in check once this move is made?
//	BackUpBoard(BACKUP);
	memcpy(BackUpSquare, Square, sizeof(int)*89);
	MakeMove(Move, FALSE);
	if (Square[MOVER]==WHITE) Square[MOVER]=BLACK; else Square[MOVER]=WHITE; // Want to see check from point of view on non-Square[MOVER]
	Checked=IsCheck();
	memcpy(Square, BackUpSquare, sizeof(int)*89);
//	BackUpBoard(RESTORE);
	if (Checked) return 2;
		else return 0;
} // end of TChessBoard::VerifyMove(TMove)

char
TChessBoard::ToPieceChar(int SquareID)
{
	switch (SquareID) {
		case EMPTY  : return('-');
		case WP : return('P');
		case WN : return('N');
		case WB : return('B');
		case WR : return('R');
		case WQ : return('Q');
		case WK : return('K');
		case BP : return('p');
		case BN : return('n');
		case BB : return('b');
		case BR : return('r');
		case BQ : return('q');
		case BK : return('k');
	}
	return 0;
}

int
TChessBoard::ToPieceValue(char SquareID)
{
	switch (SquareID) {
		case '-' : return(EMPTY);
		case ' ' : return(0);
		case 'P' : return(WP);
		case 'N' : return(WN);
		case 'B' : return(WB);
		case 'R' : return(WR);
		case 'Q' : return(WQ);
		case 'K' : return(WK);
		case 'p' : return(BP);
		case 'n' : return(BN);
		case 'b' : return(BB);
		case 'r' : return(BR);
		case 'q' : return(BQ);
		case 'k' : return(BK);
	}
   return 0;
}

void
TChessBoard::SavePGN(char* FileName, int Append, char* Event)
{
/*	char s[30];
	int i, j;
	FILE *f;
	if (Append) {
		f=fopen((const char *)FileName, "a");
		if (f!=NULL) fprintf(f, "\n\n");
	} else {
		f=fopen((const char *)FileName, "w");
	}
	if (f!=NULL) {
		int Status=GameStatus();
		TakeBackAllMoves();
		fprintf(f, "[Event \"%s\"]\n", Event);
		if (!OriginalPosition) {
			char Fen[MAXFEN];
			GetFEN(Fen);
			fprintf(f, "[FEN \"%s\"]\n", Fen);
		}
		VariantName(s);
		fprintf(f, "[Variant \"%s\"]\n", s);
		if (Resigned==BLACK || Status==1 || Status==7 || Status==8) fprintf(f, "[Result \"1-0\"]\n"); else
		if (Resigned==WHITE || Status==2 || Status==6 || Status==9) fprintf(f, "[Result \"0-1\"]\n"); else
		if (DrawAgreed || Status==3 || Status==4 || Status==5) fprintf(f, "[Result \"1/2-1/2\"]\n"); else
		fprintf(f, "[Result \"*\"]\n");
		fprintf(f, "\n");

		TakeBackAllMoves();
      if (ResetTo[MOVER]==BLACK) fprintf(f, "1.");
		for (i=1; i<=MovesStored; i++) {
			TranslateMoveToAlgebraic(s, MovesMade[i]);
			if (ResetTo[MOVER]==WHITE && i%2==1) fprintf(f, "%i.", i/2+1);
			if (ResetTo[MOVER]==BLACK && i%2==0) fprintf(f, "%i.", i/2+1);
			fprintf(f, " %s ", s);
			ReplayMove();
		}
	}
	fclose(f);
	ReplayAllMoves();
	GameSaved=TRUE;*/
}

TMoveList
TChessBoard::GetPreviousMoves()
{
	int i;
	TMoveList ReturnMoves;
	ReturnMoves.Moves.Flush();
	for (i=1; i<=MovePointer; i++) {
		ReturnMoves.Moves.Add(MovesMade[i]);
	}
	ReturnMoves.Amount=ReturnMoves.Moves.GetItemsInContainer();
	return ReturnMoves;
}

TMove
QuickAddMove(int From, int To)
{
	TMove m;
	m.From=From;
	m.To=To;
	return m;
}

int
TChessBoard::IsOriginalPosition()
{
	return OriginalPosition;
}

/*
int
TChessBoard::CreateOpeningBook(
	TWindow* caller,
	char FileName[MAXOPENINGFILES][MAXFILENAMELENGTH],
	int MaxPly,
	int MaxPositions,
	int MinResults,
	BOOL IncludeUnknownResults,
	int& Written,
	int& Games,
	int& GamesUsed,
	int& TotalPositions,
	char* Error)
{
	::MessageBox(caller->HWindow, "Save Game?", "Quit Rival", MB_YESNOCANCEL);
	int timeticker=GetTickCount();
	FENTimer=0;
	Games=0;
	GamesUsed=0;
	Written=0;
	TotalPositions=0;
	strcpy(Error, "\nCompleted Successfully");
	MaxOpeningPositions=MaxPositions;
	OpeningPositions=new TOpeningPosition[MaxOpeningPositions];
	int i, j;
	TMove move;
	FILE *f;
	MovesMade.Flush();
	WhiteClocks.Flush();
	BlackClocks.Flush();
	char line[100], FEN[MAXFEN];
	strcpy(FEN, "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w QKqk - 0 1");
	f=NULL;
	// Clear static variables in ReadPGN
	ReadPGN(f, 0);
	f=fopen((const char *)FileName[0], "r");
	// Read Moves
	TMove Move;
	int Count;
	char q[30];
	char MoveString[10];
	char c;
	int l, result;
	int MovesRead=TRUE;
	int MatchResult=UNKNOWNRESULT;
	OpeningPositionCount=0;
	while (1) {
		for (i=0; i<512; i++) buffer[i]='\0';
		result=ReadPGN(f, 0);
		while (result==1) {
			if (MovesRead) {
				Games++;
				TranslateFenToBoard(FEN, ResetTo);
				MovePointer=MovesStored=0;
				ResetBoard();
				MovesRead=FALSE;
				MatchResult=UNKNOWNRESULT;
			}
			if (strstr(buffer, "[Result")!=NULL) {
				if (strstr(buffer, "1-0")!=NULL) MatchResult=WHITEWIN; else
				if (strstr(buffer, "0-1")!=NULL) MatchResult=BLACKWIN; else
				if (strstr(buffer, "1/2-1/2")!=NULL) MatchResult=DRAW; else
				MatchResult=UNKNOWNRESULT;
				if (MatchResult!=UNKNOWNRESULT || IncludeUnknownResults) GamesUsed++;
			}
			result=ReadPGN(f, 0);
		};
		if (result==99) {
			TranslateFenToBoard(buffer, ResetTo);
			ResetBoard();
		}
		if (result==-1) goto Finished;
		if (result==0) {
			MovesRead=TRUE;
			if ((MatchResult!=UNKNOWNRESULT || IncludeUnknownResults) && MovesStored<MaxPly) {
				TranslateAlgebraicMove(buffer, move);
				if (VerifyMove(move)==0) {
					WhiteClock=0;
					BlackClock=0;
					MakeMove(move, TRUE);
					TotalPositions++;
					if (StoreOpeningPosition(MatchResult)==MAXOPENINGSREACHED) {
						writeLog("Max openings reached");
						goto Finished;
					}
				} else {
					if (strcmp(buffer, "-0")!=0 && strcmp(buffer, "-1")!=0 && strcmp(buffer, "/2-1/2")!=0) {
						sprintf(Error, "\nError: Buffer was \"%s\" Interpreted Move as \"%i to %i\"", buffer, move.From, move.To);
						writeLog(Error);
						goto Finished;
					}
				}
			}
		}
	}

Finished:
	fclose(f);
	strcpy(FEN, "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w QKqk - 0 1");
	TranslateFenToBoard(FEN, ResetTo);
	ResetBoard();
	GameSaved=TRUE;
	f=fopen(OPENINGS, "w");
	for (i=0; i<OpeningPositionCount; i++) {
		if (	OpeningPositions[i].WhiteWins+
				OpeningPositions[i].BlackWins+
				OpeningPositions[i].Draws>=MinResults) {
			fprintf(f, "%s W %i B %i D %i\n",
				OpeningPositions[i].Fen,
				OpeningPositions[i].WhiteWins,
				OpeningPositions[i].BlackWins,
				OpeningPositions[i].Draws);
			Written++;
		}
	}
	fclose(f);
	delete[] OpeningPositions;
	f=fopen("c:\\log.txt", "a");
	fprintf(f, "Total time ms %i, GetFEN %i", GetTickCount()-timeticker, FENTimer);
	fclose(f);
	return Written;
}

int
TChessBoard::StoreOpeningPosition(int MatchResult)
{
	int i;
	BOOL Found=FALSE;
	// Get Fen Translation
	char Fen[MAXFEN];
	GetFEN(Fen);
	// Do we have this position already?
	for (i=0; i<OpeningPositionCount; i++) {
		if (strcmp(OpeningPositions[i].Fen, Fen)==0) {
			Found=TRUE;
			break;
		}
	}
	// Subtract one for the correct index
	if (Found) {
		switch (MatchResult) {
			case WHITEWIN 	: OpeningPositions[i].WhiteWins++; break;
			case BLACKWIN 	: OpeningPositions[i].BlackWins++; break;
			case DRAW 		: OpeningPositions[i].Draws++; break;
		}
	} else {
		if (OpeningPositionCount<MaxOpeningPositions) {
			strcpy(OpeningPositions[OpeningPositionCount].Fen, Fen);
			OpeningPositions[OpeningPositionCount].WhiteWins=(MatchResult==WHITEWIN);
			OpeningPositions[OpeningPositionCount].BlackWins=(MatchResult==BLACKWIN);
			OpeningPositions[OpeningPositionCount].Draws=(MatchResult==DRAW);
			OpeningPositionCount++;
		} else {
			return MAXOPENINGSREACHED;
		}
	}
	return 0;
} */

int
TChessBoard::TranslateFenToBoard(char* s, int* SetupBoard)
{
	unsigned int count;
	char c;
	int rank;
	int i;

	for (i=0; i<11; i++)
		SetupBoard[i]=0;

	for (i=11; i<89; i++)
		SetupBoard[i]=EMPTY;

	SetupBoard[WKINGMOVED]=TRUE;
	SetupBoard[WROOK1MOVED]=TRUE;
	SetupBoard[WROOK8MOVED]=TRUE;
	SetupBoard[BROOK1MOVED]=TRUE;
	SetupBoard[BROOK8MOVED]=TRUE;
   SetupBoard[BKINGMOVED]=TRUE;

	if (strlen(s)<1) return -1;
	rank=8;
	count=0;
	while (s[count]==' ') count++;
   count--;
	while (rank>=1) {
			if (++count>strlen(s)-1) return -1;
			c=s[count];
			int sq=rank;
			while (c!='/' && c!=' ') {
				//char t[30];
				//sprintf(t, "%c %i", c, sq);
				switch (c) {
					case 'P' : sq+=10; if (sq>90) return -1; SetupBoard[sq]=WP; break;
					case 'Q' : sq+=10; if (sq>90) return -1; SetupBoard[sq]=WQ; break;
					case 'B' : sq+=10; if (sq>90) return -1; SetupBoard[sq]=WB; break;
					case 'N' : sq+=10; if (sq>90) return -1; SetupBoard[sq]=WN; break;
					case 'R' : sq+=10; if (sq>90) return -1; SetupBoard[sq]=WR; break;
					case 'K' : sq+=10; if (sq>90) return -1; SetupBoard[sq]=WK; break;
					case 'p' : sq+=10; if (sq>90) return -1; SetupBoard[sq]=BP; break;
					case 'q' : sq+=10; if (sq>90) return -1; SetupBoard[sq]=BQ; break;
					case 'b' : sq+=10; if (sq>90) return -1; SetupBoard[sq]=BB; break;
					case 'n' : sq+=10; if (sq>90) return -1; SetupBoard[sq]=BN; break;
					case 'r' : sq+=10; if (sq>90) return -1; SetupBoard[sq]=BR; break;
					case 'k' : sq+=10; if (sq>90) return -1; SetupBoard[sq]=BK; break;
					default :
						if (c>='0' && c<='8') {
							sq+=10*((int)(c-'0'));
							if (sq>90) return -1;
						} else {
							return -1;
						}
				}
				if (++count>strlen(s)-1) return -1;
				c=s[count];
			}
			rank--;
		}
		// not enough ranks
		if (rank!=0) return -1;
		while (s[count]!=' ') count++; while (s[count]==' ') count++;
		if (s[count]=='w') SetupBoard[MOVER]=WHITE; else
			if (s[count]=='b') SetupBoard[MOVER]=BLACK; else
				return -1;
		while (s[count]!=' ') count++; while (s[count]==' ') count++;
		while (s[count]!=' ') {
			switch(s[count]) {
				case 'K' : SetupBoard[WKINGMOVED]=FALSE; SetupBoard[WROOK8MOVED]=FALSE; break;
				case 'Q' : SetupBoard[WKINGMOVED]=FALSE; SetupBoard[WROOK1MOVED]=FALSE; break;
				case 'q' : SetupBoard[BKINGMOVED]=FALSE; SetupBoard[BROOK8MOVED]=FALSE; break;
				case 'k' : SetupBoard[BKINGMOVED]=FALSE; SetupBoard[BROOK1MOVED]=FALSE; break;
			}
			if (++count>strlen(s)-1) return 1;
		}
		while (s[count]!=' ') count++; while (s[count]==' ') count++;
		while (s[count]!=' ') {
			if (s[count]>='a' && s[count]<='h') {
				SetupBoard[ENPAWN]=s[count]-'a'+1;
			}
			if (++count>strlen(s)-1) return 1;
		}
		while (s[count]!=' ') count++; while (s[count]==' ') count++;
		SetupBoard[FIFTYMOVES]=0;
		int tencount=0;
		while (s[count]!=' ') {
			if (s[count]>='1' && s[count]<='8') {
				SetupBoard[FIFTYMOVES]=(10*tencount*SetupBoard[FIFTYMOVES])+s[count]-'0';
				tencount++;
			}
			if (++count>strlen(s)-1) return 1;
	}
	return 1;
}

void
TChessBoard::TranslateMoveToAlgebraic(char *s, TMove Move)
{
	int Count=-1;
	int FromSquares[50];
	int ToSquareCount=0;
	int i;
	for (i=0; i<10; i++) s[i]='\0';
	// castle?
	if (Square[Move.From]%100==KING && abs(GetX(Move.To)-GetX(Move.From))>1) {
		s[++Count]='o';
		s[++Count]='-';
		s[++Count]='o';
		if (Move.To==31 || Move.To==38) {
			s[++Count]='-';
			s[++Count]='o';
		}
	} else
	// pawns
	if (Square[Move.From]%100==PAWN) {
		if (GetX(Move.From)==GetX(Move.To)) {
			s[++Count]=GetX(Move.To)+'a'-1;
			s[++Count]=GetY(Move.To)+'0';
		} else {
			// must be a capture
			s[++Count]=GetX(Move.From)+'a'-1;
			s[++Count]='x';
			s[++Count]=GetX(Move.To)+'a'-1;
			s[++Count]=GetY(Move.To)+'0';
		}
		if (GetY(Move.To)==1 || GetY(Move.To)==8) {
			s[++Count]='=';
			switch (Move.PromotionPiece%100) {
				case KING : s[++Count]='K'; break;
				case ROOK : s[++Count]='R'; break;
				case KNIGHT : s[++Count]='N'; break;
				case BISHOP : s[++Count]='B'; break;
				case QUEEN : s[++Count]='Q'; break;
			}
		}
	} else {
		switch (Square[Move.From]%100) {
			case KING : s[++Count]='K'; break;
			case QUEEN : s[++Count]='Q'; break;
			case KNIGHT : s[++Count]='N'; break;
			case ROOK : s[++Count]='R'; break;
			case BISHOP : s[++Count]='B'; break;
		}
		// Is the "to" square enough
		TMoveList LegalMoves;
		int MoveCount=GetMoveList(LegalMoves);
		for (i=1; i<=MoveCount; i++) {
			if (LegalMoves.Moves[i].To==Move.To) {
				if (Square[LegalMoves.Moves[i].From]==Square[Move.From]) {
					FromSquares[(++ToSquareCount)-1]=LegalMoves.Moves[i].From;
				}
			}
		}
		if (ToSquareCount==0) return;
		if (ToSquareCount==1) {
			if (Square[Move.To]!=EMPTY) s[++Count]='x';
			s[++Count]=GetX(Move.To)+'a'-1;
			s[++Count]=GetY(Move.To)+'0';
		} else {
			int NeedRank=FALSE;
			int NeedFile=FALSE;
			// Do we need a particular reference?
			for (int a=0; a<ToSquareCount; a++) {
				if (GetX(FromSquares[a])==GetX(Move.From) && FromSquares[a]!=Move.From) NeedRank=TRUE;
				if (GetY(FromSquares[a])==GetY(Move.From) && FromSquares[a]!=Move.From) NeedFile=TRUE;
			}
			// if not, use rank
			if (!NeedRank && !NeedFile) NeedFile=TRUE;
			if (NeedFile) s[++Count]=GetX(Move.From)+'a'-1;
			if (NeedRank) s[++Count]=GetY(Move.From)+'0';
			if (Square[Move.To]!=EMPTY) s[++Count]='x';
			s[++Count]=GetX(Move.To)+'a'-1;
			s[++Count]=GetY(Move.To)+'0';
		}
	}
	BackUpBoard(BACKUP);
	MakeMove(Move, FALSE);
	BackUpBoard(RESTORE);
}

void
TChessBoard::SetResigned(int Colour)
{
	Resigned=Colour;
}

void
TChessBoard::SetDrawAgreed(int agreed)
{
	DrawAgreed=agreed;
}

void
TChessBoard::GetFEN(char* s, int NoMovesMade, int ShortVersion)
{
	strcpy_s(s, 0, "");
	char t[2];
	t[1]='\0';
	int spaces;
	for (int i=18; i>=11; i--) {
		spaces=0;
		for (int j=i; j<=i+70; j+=10) {
			 switch (Square[j]) {
				case WP : if (spaces>0) { t[0]=spaces+'0'; strcat_s(s, strlen(t), t); spaces=0; } strcat_s(s, 1, "P"); break;
				case WK : if (spaces>0) { t[0]=spaces+'0'; strcat_s(s, strlen(t), t); spaces=0; } strcat_s(s, 1, "K"); break;
				case WN : if (spaces>0) { t[0]=spaces+'0'; strcat_s(s, strlen(t), t); spaces=0; } strcat_s(s, 1, "N"); break;
				case WB : if (spaces>0) { t[0]=spaces+'0'; strcat_s(s, strlen(t), t); spaces=0; } strcat_s(s, 1, "B"); break;
				case WR : if (spaces>0) { t[0]=spaces+'0'; strcat_s(s, strlen(t), t); spaces=0; } strcat_s(s, 1, "R"); break;
				case WQ : if (spaces>0) { t[0]=spaces+'0'; strcat_s(s, strlen(t), t); spaces=0; } strcat_s(s, 1, "Q"); break;
				case BP : if (spaces>0) { t[0]=spaces+'0'; strcat_s(s, strlen(t), t); spaces=0; } strcat_s(s, 1, "p"); break;
				case BK : if (spaces>0) { t[0]=spaces+'0'; strcat_s(s, strlen(t), t); spaces=0; } strcat_s(s, 1, "k"); break;
				case BN : if (spaces>0) { t[0]=spaces+'0'; strcat_s(s, strlen(t), t); spaces=0; } strcat_s(s, 1, "n"); break;
				case BB : if (spaces>0) { t[0]=spaces+'0'; strcat_s(s, strlen(t), t); spaces=0; } strcat_s(s, 1, "b"); break;
				case BR : if (spaces>0) { t[0]=spaces+'0'; strcat_s(s, strlen(t), t); spaces=0; } strcat_s(s, 1, "r"); break;
				case BQ : if (spaces>0) { t[0]=spaces+'0'; strcat_s(s, strlen(t), t); spaces=0; } strcat_s(s, 1, "q"); break;
				default : spaces++;
			 }
		}
		if (spaces>0 && !ShortVersion) {
			t[0]=spaces+'0';
			strcat_s(s, strlen(t), t);
		}
		if (i!=11) strcat_s(s, 1, "/");
	}
	strcat_s(s, 1, " ");
	if (GetMover()==WHITE) strcat_s(s, 1, "w"); else strcat_s(s, 1, "b");
	strcat_s(s, 1, " ");
	int NoCastle=TRUE;
	if (!Square[WKINGMOVED]) {
		if (!Square[WROOK1MOVED]) {
			strcat_s(s, 1, "Q");
			NoCastle=FALSE;
		}
		if (!Square[WROOK8MOVED]) {
			strcat_s(s, 1, "K");
			NoCastle=FALSE;
		}
	}
	if (!Square[BKINGMOVED]) {
		if (!Square[BROOK1MOVED]) {
			strcat_s(s, 1, "q");
			NoCastle=FALSE;
		}
		if (!Square[BROOK8MOVED]) {
			strcat_s(s, 1, "k");
			NoCastle=FALSE;
		}
	}
	if (NoCastle) strcat_s(s, 1, "-");
	strcat_s(s, 1, " ");
	char tt[5];
	if (Square[ENPAWN]) {
		sprintf_s( tt, "%c%c", (char)(Square[ENPAWN]+'a'-1), GetMover()==WHITE ? '6' : '3' );
		strcat_s(s, strlen(tt), tt);
	} else {
		strcat_s(s, 1, "-");
	}
	strcat_s(s, 1, " ");

	if (NoMovesMade) 
	{
		strcat_s(s, 1, "0");
	}
	else 
	{
		_itoa_s(Square[FIFTYMOVES], tt, 4, 10);
		strcat_s(s, 4, tt);
	}
	strcat_s(s, 1, " ");

	if (NoMovesMade) 
	{
		strcat_s(s, 1, "0");
	}
	else 
	{
		_itoa_s((MovePointer+2)/2, tt, 4, 10);
		strcat_s(s, 4, tt);
	}
}
