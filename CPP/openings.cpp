#pragma unmanaged

#include "openings.h"
#include "newrival.h"
#include "logger.h"
#include "chessbrd.h"

TOpeningPosition* OpeningPositions;
int CachedOpenings;
int SetupBoard[89];

#define MAXREPLIES 2000

bool GetOpening(TChessBoard* Game, TMove& Move)
{
	TMoveList List;
	int i, j;
	char Fen[MAXFEN];
	TMove Reply[MAXREPLIES];
	int ReplyIndexes[MAXREPLIES];
	int Replies=0;
	int GamesPlayed;
	bool GoAhead;
	float Percentage;

#ifdef VERBOSE_LOGGING
	WriteLog("Trying Openings");
#endif
	bool WhiteToMove=Game->GetMover()==WHITE;
	memcpy((void *)SetupBoard, (void *)Game->Square, 89*sizeof(int));
	TChessBoard* TempGame=new TChessBoard(SetupBoard);
	int MoveCount=Game->GetMoveList(List);
	for (i=1; i<=MoveCount; i++) {
		TempGame->MakeMove(List.Moves[i], TRUE);
		TempGame->GetFEN(Fen, TRUE, TRUE);
		for (j=0; j<CachedOpenings; j++) {
			if (strcmp(Fen, OpeningPositions[j].Fen)==0) {
				GamesPlayed=OpeningPositions[j].WhiteWins+OpeningPositions[j].BlackWins+OpeningPositions[j].Draws;
				GoAhead=(GamesPlayed<20);
				if (!GoAhead) {
					if (GamesPlayed==0)
					{
						Percentage = 0;
					}
					else
					{
						if (WhiteToMove) {
							Percentage=((float)OpeningPositions[j].WhiteWins/(float)GamesPlayed);
							GoAhead=((Percentage*100)>30);
						} else {
							Percentage=((float)OpeningPositions[j].BlackWins/(float)GamesPlayed);
							GoAhead=((Percentage*100)>20);
						}
					}
				}
				if (GoAhead) {                   
					ReplyIndexes[Replies]=j;
					Reply[Replies++]=List.Moves[i];
					if (Replies==MAXREPLIES) goto done;
				}
			}
		}
		TempGame->TakeBackMove();
	}
done:
	delete TempGame;
	if (Replies==0) {
#ifdef VERBOSE_LOGGING
		WriteLog("No more openings");
#endif
		return(FALSE);
	}
	int ReplyNum=rand() % (Replies-1);
	Move=Reply[ReplyNum];
	Move.PromotionPiece=EMPTY;
	return(Game->VerifyMove(Move)==0);
}

void CacheOpenings(char* filename)
{
	int j;
	char s[10][MAXFEN];
	char FileFen[MAXFEN];
	int w, b, d;
	CachedOpenings=0;
	FILE* f;

	fopen_s(&f, filename, "r");
	while (fscanf_s(f, "%s%s%s%s%s%s%s%i%s%i%s%i", &s[0],&s[1],&s[2],&s[3],&s[4],&s[5],&s[6],&w,&s[8],&b,&s[9],&d) != EOF) 
	{
		CachedOpenings++;
	}
	fclose(f);
	OpeningPositions=new TOpeningPosition[CachedOpenings];
	CachedOpenings=0;

	fopen_s(&f, filename, "r");
	while (fscanf_s(f, "%s%s%s%s%s%s%s%i%s%i%s%i",
				&s[0],&s[1],&s[2],&s[3],&s[4],&s[5],&s[6],&w,&s[8],&b,&s[9],&d)!=EOF) {
		strcpy_s(FileFen, 0, "");
		for (j=0; j<4; j++) {
			strcat_s(FileFen, s[j]);
			strcat_s(FileFen, " ");
		}
		strcat_s(FileFen, "0 0");
#ifdef DYNAMICFEN
		OpeningPositions[CachedOpenings].Fen = new char[strlen(FileFen)+1];
#endif
		strcpy_s(OpeningPositions[CachedOpenings].Fen, strlen(FileFen), FileFen);
		OpeningPositions[CachedOpenings].WhiteWins=w;
		OpeningPositions[CachedOpenings].BlackWins=b;
		OpeningPositions[CachedOpenings].Draws=d;
		CachedOpenings++;
	}
	fclose(f);
}

void DeleteOpeningPositions()
{
	if (OpeningPositions!=NULL) {
#ifdef DYNAMICFEN
		for (int i=0; i<Total; i++) {
			delete[] OpeningPositions[i].Fen;
		}
#endif
		delete[] OpeningPositions;
	}
	OpeningPositions=NULL;
}
