#pragma unmanaged

#include <stdio.h>
//#include <vld.h>
#include <stdlib.h>
#include <string.h>
#include <direct.h> // for getcwd
#include <windows.h>
#include <time.h>
#include <string>
#include "newrival.h"
#include "searcher.h"
#include "logger.h"
#include "openings.h"

using namespace std;

int TotalNodes = 0;

bool g_isSearching = false;

string SearchMoves[MAX_COMMAND_WORDS];
string SearchWords[MAX_COMMAND_WORDS];
string PositionWords[MAX_COMMAND_WORDS];
string OptionWords[MAX_COMMAND_WORDS];

char logtextnewrival[LOGTEXTSIZE];

char s[STRING_SIZE];

bool ExitApplication = false;
bool UseOpeningLibrary = false;
bool isDebugMode;
TSearcher* Searcher = 0;
//int hashSize = 2000;
//int hashSize = 65535;
int hashSize = 37268;
//int hashSize = 1048576;
TChessBoard* Game;

void LoopForCommandsAndProcess();

void SendToGUI(string info)
{
	printf("%s\n", info.c_str());
	fflush(stdout);
	char s[200];
	sprintf_s(s, "%s", info.c_str());
}

int Split(char* CommandString, string* ReturnArray)
{
	int i;
	int count = 0;
	int length = strlen(CommandString);

	for (i=0; i<MAX_COMMAND_WORDS; i++)
	{
		ReturnArray[i] = "";
	}

	for (i=0; i<length; i++)
	{
		if (	
			CommandString[i] != ' ' && 
			CommandString[i] != '\n' && 
			CommandString[i] != '\r' &&
			CommandString[i] != '\t')
		{
			ReturnArray[count] += CommandString[i];
		}
		else
		{
			if (CommandString[i] == '\n')
			{
				break;
			}
			// don't move count on until new word is found
			if (ReturnArray[count].length() > 0)
			{
				count ++;
			}
		}
	}
	count++;

	return count;
}

bool IsKeyword(string word)
{
	return
		word.compare("searchmoves") == 0 ||
		word.compare("ponder") == 0 ||
		word.compare("wtime") == 0 ||
		word.compare("btime") == 0 ||
		word.compare("winc") == 0 ||
		word.compare("binc") == 0 ||
		word.compare("movestogo") == 0 ||
		word.compare("depth") == 0 ||
		word.compare("nodes") == 0 ||
		word.compare("mate") == 0 ||
		word.compare("movetime") == 0 ||
		word.compare("infinite") == 0;
}

void Search(char* UciCommandString)
{
	bool isGatheringSearchMoves = false;
	bool isPonder = false, isSearchForMate = false, isInfiniteSearch = false;
	int whiteMillisRemaining = -1, blackMillisRemaining = -1;
	int whiteIncrementMillis = 0, blackIncrementMillis = 0;
	int movesToGoToTimeControl = -1;
	int maxSearchDepth = -1;
	int maxSearchNodes = -1;
	int timeToMoveMillis = -1;
	int moveCount = 0;

	int wordCount = Split(UciCommandString, SearchWords);

		for (int i=0; i<wordCount; i++)
		{
			string word = SearchWords[i];
			if (IsKeyword(word))
			{
				if (!word.compare("searchmoves"))
				{
					isGatheringSearchMoves = true;
				}
				else if (!word.compare("ponder"))
				{
					isGatheringSearchMoves = false;
					isPonder = true;
				}
				else if (!word.compare("wtime"))
				{
					isGatheringSearchMoves = false;
					whiteMillisRemaining = atoi(SearchWords[i + 1].c_str());
				}
				else if (!word.compare("btime"))
				{
					isGatheringSearchMoves = false;
					blackMillisRemaining = atoi(SearchWords[i + 1].c_str());
				}
				else if (!word.compare("winc"))
				{
					isGatheringSearchMoves = false;
					whiteIncrementMillis = atoi(SearchWords[i + 1].c_str());
				}
				else if (!word.compare("binc"))
				{
					isGatheringSearchMoves = false;
					blackIncrementMillis = atoi(SearchWords[i + 1].c_str());
				}
				else if (!word.compare("movestogo"))
				{
					isGatheringSearchMoves = false;
					movesToGoToTimeControl = atoi(SearchWords[i + 1].c_str());
				}
				else if (!word.compare("depth"))
				{
					isGatheringSearchMoves = false;
					maxSearchDepth = atoi(SearchWords[i + 1].c_str());
				}
				else if (!word.compare("nodes"))
				{
					isGatheringSearchMoves = false;
					maxSearchNodes = atoi(SearchWords[i + 1].c_str());
				}
				else if (!word.compare("mate"))
				{
					isGatheringSearchMoves = false;
					isSearchForMate = true;
				}
				else if (!word.compare("movetime"))
				{
					isGatheringSearchMoves = false;
					timeToMoveMillis = atoi(SearchWords[i + 1].c_str());
				}
				else if (!word.compare("infinite"))
				{
					isGatheringSearchMoves = false;
					isInfiniteSearch = true;
				}
			}
			else if (isGatheringSearchMoves)
			{
				SearchMoves[moveCount++] = word;
			}
		}

		Searcher->SetSearchMoves(SearchMoves);
		Searcher->SetPonderMode(isPonder);
		Searcher->SetWhiteMillisRemaining(whiteMillisRemaining);
		Searcher->SetBlackMillisRemaining(blackMillisRemaining);
		Searcher->SetWhiteIncrementMillis(whiteIncrementMillis);
		Searcher->SetBlackIncrementMillis(blackIncrementMillis);
		Searcher->SetMovesToGoToTimeControl(movesToGoToTimeControl);
		Searcher->SetMaxSearchNodes(maxSearchNodes);
		Searcher->SetisSearchingForMate(isSearchForMate);
		Searcher->SetMaxMoveTimeMillis(timeToMoveMillis);

		int millisRemaining = (Searcher->IsWhiteToMove() ? whiteMillisRemaining : blackMillisRemaining);
		int incrementMillis = (Searcher->IsWhiteToMove() ? whiteIncrementMillis : blackIncrementMillis);
		int searchTimeMillis;
		int ExtendedSearchTimeMillis = 0;

		if (timeToMoveMillis != -1)
		{
			searchTimeMillis = timeToMoveMillis - 100;
		}
		else if (maxSearchDepth != -1)
		{
			Searcher->SetMaxDepth(maxSearchDepth);
			Searcher->SetSearchTimeMillis(-1);
		}
		else if (isInfiniteSearch)
		{
			Searcher->SetMaxDepth(MAXDEPTH-1);
			Searcher->SetSearchTimeMillis(-1);
		}
		else 
		{
			if (incrementMillis > 0)
			{
				if (millisRemaining > 2000)
				{
					searchTimeMillis = (int)(min(incrementMillis * 2, millisRemaining / 2.0));
				}
				else
				{
					searchTimeMillis = incrementMillis;
				}
			}
			else
			{
				int baseTimeMillis;
				if (movesToGoToTimeControl == -1)
				{
					// no increment, no additional time after this is used up
					baseTimeMillis = (millisRemaining - 3000) / 24;
				}
				else
				{
					// standard time controls, take off a few milliseconds for safety
					baseTimeMillis = (millisRemaining - 3000) / movesToGoToTimeControl - 250;
				}
				searchTimeMillis = baseTimeMillis;
			}

			if (searchTimeMillis <= 0)
			{
				searchTimeMillis = (millisRemaining / 4) - 250;
			}

			if (searchTimeMillis <= 0)
			{
				searchTimeMillis = 100;
			}

			if (millisRemaining > searchTimeMillis * 4)
			{
				ExtendedSearchTimeMillis = searchTimeMillis;
			}
		}

#ifdef TESTING
		sprintf_s(s, "Search Time = %i", searchTimeMillis);
		std::cout << s << "\r\n";
		sprintf_s(s, "Extended Search Time = %i", ExtendedSearchTimeMillis);
		std::cout << s << "\r\n";
#endif
		Searcher->SetSearchTimeMillis(searchTimeMillis);
		Searcher->SetMaxExtendedSearchTimeMillis(searchTimeMillis + ExtendedSearchTimeMillis);

		bool OpeningMoveFound = false;
		TMove BestMove;
		TMove OpeningMove;

		if (UseOpeningLibrary)
		{
			OpeningMoveFound = GetOpening(Game, OpeningMove);
		}

		if (OpeningMoveFound)
		{
			BestMove = OpeningMove;
		}
		else
		{
			g_isSearching = true;

#ifdef TESTING
			cout << "Current Evaluation = " << Searcher->Evaluate() << LOG_ENDL;
#endif
#ifdef STALEHASHTABLEBEFOREMOVE
			Searcher->StaleHashTable();
#endif

			TPath Path = Searcher->Search();

			g_isSearching = false;
			BestMove = Path.Move[0];
		}

		char moveString[7];
		Searcher->GetSimpleMoveString(BestMove, moveString);

		char messageText[STRING_SIZE];
		sprintf_s(messageText, "bestmove %s\n", moveString);

		SendToGUI(messageText);

#ifdef TESTING
		int t = GetTickCount() - Searcher->GetSearchStartTime();
		TPath PrincipalPath = Searcher->GetPrincipalPath();

		TotalNodes += PrincipalPath.Nodes;

		printf("Nodes %i\r\n", PrincipalPath.Nodes);
		printf("Score %i\r\n", PrincipalPath.Move[0].Score);
		printf("Time %i\r\n", t);
		if (t > 0)
		{
			int d = t / 1000;
			if (d == 0)
			{
				d = 1;
			}
			printf("NPS %i\r\n", PrincipalPath.Nodes / d);
		}

		cout << LOG_ENDL << "Total Nodes = " << TotalNodes << LOG_ENDL;
#endif
}

void SetPosition(char* UciCommandString)
{
	int i;
	int moveListStartPosition = 0;
	
#ifdef VERBOSE_LOGGING
	WriteLog("Splitting Comand String");
#endif
	int wordCount = Split(UciCommandString, PositionWords);

	delete Game;

	if (!PositionWords[1].compare("startpos"))
	{
#ifdef VERBOSE_LOGGING
		WriteLog("Creating chessboard");
#endif
		Game = new TChessBoard();
	}
	else
	{
#ifdef VERBOSE_LOGGING
		WriteLog("Interpreting FEN");
#endif
		char s[STRING_SIZE];
		string fenString;
		for (i=1; i<wordCount; i++)
		{
			if (PositionWords[i].compare("moves") != 0)
			{
				if (PositionWords[i].compare("fen") != 0)
				{
					fenString.append(PositionWords[i].append(" "));
				}
			}
			else
			{
				break;
			}
		}
		sprintf_s(s, "%s", fenString.c_str());
#ifdef VERBOSE_LOGGING
		WriteLog("Creating chessboard with FEN");
#endif
		Game = new TChessBoard(s);
	}

	for (i = 0; i < wordCount; i++)
	{
		if (!PositionWords[i].compare("moves"))
		{
			moveListStartPosition = i + 1;
		}
	}

	if (moveListStartPosition > 0)
	{
		for (i = moveListStartPosition; i < wordCount; i++)
		{
			TMove move;
			string word = PositionWords[i];
			if (word.length() >= 4)
			{
				move.From = ((int)(word[0])-'a'+1) * 10 + ((int)(word[1])-'0');
				move.To = ((int)(word[2])-'a'+1) * 10 + ((int)(word[3])-'0');
				if (word.length() > 4)
				{
					switch (word[4])
					{
						case 'q' : move.PromotionPiece = QUEEN; break;
						case 'n' : move.PromotionPiece = KNIGHT; break;
						case 'r' : move.PromotionPiece = ROOK; break;
						case 'b' : move.PromotionPiece = BISHOP; break;
						case 'Q' : move.PromotionPiece = QUEEN; break;
						case 'N' : move.PromotionPiece = KNIGHT; break;
						case 'R' : move.PromotionPiece = ROOK; break;
						case 'B' : move.PromotionPiece = BISHOP; break;
					}
				}

				//sprintf_s(logtextnewrival, LOGTEXTSIZE, "About to move %s", word.c_str());
				//WriteLog(logtextnewrival);
				//if (Game->VerifyMove(move))
				if (true)
				{
					Game->MakeMove(move, true);
				}
				else
				{
					cout << (int)move.From << " to " << (int)move.To << " is illegal" << LOG_ENDL;
				}
				//WriteLog("Success");
			}
		}
	}

#ifdef VERBOSE_LOGGING
	WriteLog("Setting initial position");
	cout << "Searcher is " << Searcher << LOG_ENDL;
#endif
	Searcher->SetInitialPosition(*Game);
}

void NewGame()
{
	delete Searcher;
	Searcher = new TSearcher(hashSize);

	Searcher->SetMaxDepth(MAXDEPTH-1);
	Searcher->SetMaxQuiesceDepth(50);

	Searcher->SetUseNullMove(DEFAULT_USE_NULL_MOVE);
	Searcher->SetNullMoveStopMaterial(DEFAULT_NULL_MOVE_STOP_MATERIAL);
	Searcher->SetNullMoveReduceDepth(DEFAULT_NULL_MOVE_REDUCE_DEPTH);

	Searcher->SetUseCheckExtensions(DEFAULT_USE_CHECK_EXTENSIONS);
	Searcher->SetUsePawnPushExtensions(DEFAULT_USE_PAWNPUSH_EXTENSIONS);

	Searcher->SetUseFailHighReductions(DEFAULT_USE_FAIL_HIGH_REDUCTIONS);

	Searcher->SetContempt(-75);
	Searcher->SetUseHistory(DEFAULT_USE_HISTORY);
	Searcher->SetUseSingleReplyExtensions(0);
	Searcher->SetRandomMoveOrder(DEFAULT_RANDOM_MOVE_ORDER);
	Searcher->SetHashReadReduce(0);
	Searcher->SetHashWriteReduce(0);
	Searcher->SetUseMinimalWindow(1);
	
	Searcher->SetMaxExtensions(DEFAULT_MAX_EXTENSIONS);
	Searcher->SetAspireWindow(DEFAULT_ASPIRE_WINDOW);

	Searcher->ClearHashTable();
	Searcher->StaleHashTable();
}

void SetOption(char* UciCommandString)
{
	int wordCount = Split(UciCommandString, OptionWords);

	if (!OptionWords[1].compare("name"))
	{
		if (wordCount == 5 && !OptionWords[2].compare("Hash") && !OptionWords[3].compare("value"))
		{
			hashSize = atoi(OptionWords[4].c_str()) * 1024;
			NewGame();
		}
		if (wordCount == 4 && !OptionWords[2].compare("Clear") && !OptionWords[3].compare("Hash"))
		{
			if (Searcher)
			{
				Searcher->ClearHashTable();
			}
		}
	}
}

void ChangeDebugMode(bool isOn)
{
	isDebugMode = isOn;
}

void InitialSetup()
{
	isDebugMode = false;
}

 void StopSearch()
{
}

void ProcessCommand(char* CommandString)
{
#ifdef LOG_COMMUNICATIONS
	std::ofstream out(LOG_FILE, ios_base::app);
	out << "GUI Says: " << CommandString << COMMAND_ENDL;
	out.close();
#endif
	
	string CommandArray[MAX_COMMAND_WORDS];
	int wordCount = Split(CommandString, CommandArray);
	string CommandVerb = CommandArray[0];

	if (CommandVerb.length() > 0)
	{
		if (!CommandVerb.compare("uci"))
		{
			SendToGUI("id name Rival 1.17");
			SendToGUI("id author Chris Moreton");
			SendToGUI("option name Hash type spin min 1 max 1024 default 32");
			SendToGUI("option name Clear Hash type button");
			SendToGUI("uciok");
		}
		else if (!CommandVerb.compare("debug"))
		{
			ChangeDebugMode(!CommandArray[1].compare("on")); 
		}
		else if (!CommandVerb.compare("setoption"))
		{	
			SetOption(CommandString); 
		}
		else if (!CommandVerb.compare("register"))
		{
		}
		else if (!CommandVerb.compare("isready"))
		{
			SendToGUI("readyok");
		}
		else if (!CommandVerb.compare("ucinewgame"))
		{
			NewGame();
		}
		else if (!CommandVerb.compare("position"))
		{
#ifdef VERBOSE_LOGGING
			WriteLog("Setting Position");
#endif
			SetPosition(CommandString);
#ifdef VERBOSE_LOGGING
			WriteLog("Position Set");
#endif
		}
		else if (!CommandVerb.compare("go"))
		{
			Search(CommandString);
		}
		else if (!CommandVerb.compare("stopsearch"))
		{
			StopSearch();
		}
		else if (!CommandVerb.compare("ponderhit"))
		{
		}
		else if (!CommandVerb.compare("quit"))
		{
			ExitApplication = true;
		}
		else if (!CommandVerb.compare("stop"))
		{
			if (Searcher)
			{
				Searcher->ExitWithMove();
			}
		}
	}
}

void ProcessCommandIfAvailable()
{
	char* CommandString = new char[STRING_SIZE];
	fgets(CommandString, STRING_SIZE, stdin);
	//scanf_s("%s", CommandString, 500);

	if (strlen(CommandString)  > 0)
	{
		ProcessCommand(CommandString);
	}

	delete[] CommandString;
}

void LoopForCommandsAndProcess()
{
	while (!ExitApplication)
	{
		ProcessCommandIfAvailable();
	}
}

void PrepareOpenings()
{
	char OpeningPath[MAXFILENAMELENGTH];
	OpeningPath[0] = '\0';
	char WorkingDirectory[MAXFILENAMELENGTH];

	if (_getcwd(WorkingDirectory, sizeof(WorkingDirectory))==NULL) {
		strcpy_s(WorkingDirectory, 3, ".\\");
	}
	if (strlen(WorkingDirectory)>0) {
		if (WorkingDirectory[strlen(WorkingDirectory)-1]=='\\') {
			WorkingDirectory[strlen(WorkingDirectory)-1]='\0';
		}
	}

	strcat_s(OpeningPath, WorkingDirectory);
	strcat_s(OpeningPath, "\\rival.opn");

	CacheOpenings("c:\\documents and settings\\chris\\my documents\\Visual Studio 2005\\projects\\RivalClassic\\debug\\rival.opn");
}

void Test()
{

	for (int i=0; i<1; i++)
	{
		int t = GetTickCount();

		//ProcessCommand("position r1bq1bnr/1ppp1kpp/p1n5/1B2pp2/4P3/5N1P/PPPP1PP1/RNBQ1RK1 w - - 1 6");
		//ProcessCommand("go depth 3");

		//NewGame();

		// 2.3m nodes vs 2.2m without PST
		//ProcessCommand("position r3k1nr/pp2ppbp/6p1/3pP3/Q2n1P2/4BB2/Pq1N2PP/R3K2R b QKqk - 1 4"); 
		//ProcessCommand("go depth 10");

		// 
		//ProcessCommand("position startpos moves e2e4 e7e6"); 
		//ProcessCommand("go depth 8");

		//NewGame();
		
		// 7.6m nodes vs 9.7m without PST
		//ProcessCommand("position startpos moves g1f3 e7e6 e2e4 d7d5 e4d5 e6d5 f1e2 f8d6"); 
		//ProcessCommand("go depth 8");

		//NewGame();

		// 4.3m nodes vs 3.5m without PST
		//ProcessCommand("position startpos moves e2e4 b8c6 g1f3 d7d5 e4d5 d8d5 b1c3 d5e6 f1e2 c8d7 d2d4 e6f5 e1g1 c6b4 e2c4 f5c2 f3e5 c2d1 c4f7 e8d8 f1d1 b4c2 a1b1 c2b4 f7d5 b4d5 e5f7 d8c8 c3d5 d7e6 f7h8 e6d5 c1f4 g7g5 f4e5 g8f6 b1c1 f8g7 c1c7 c8d8 e5f6 g7f6 c7c5 d5a2 d1a1 a2e6 a1e1 d8d7 c5b5 b7b6 h2h4 g5h4 d4d5 e6g8 e1e4 d7d6 e4e3 f6h8 e3h3 h8f6 h3d3 a8c8 d3d1 c8c5 b5c5 b6c5 b2b3 g8d5 d1d3 d6c6 f2f4 a7a5 g1f2 d5f7 f2e1 c6b5 e1d2 b5b4 d2c1 f7b3 d3d7 c5c4 d7d2 c4c3 d2d3 b4a3 d3e3 c3c2 e3e1 f6b2 c1d2 c2c1q");
		//ProcessCommand("go depth 3");

		//NewGame();

		// 1.5m nodes vs 2.5m without PST
		//ProcessCommand("position startpos"); 
		//ProcessCommand("go depth 8");

		//NewGame();

		// 1.5m nodes vs 2.5m without PST
		//ProcessCommand("position 6R1/8/7k/5p2/6p1/4K2p/8/8 w - - 0 1"); 
		//ProcessCommand("go depth 8");

		//NewGame();

		// Needs to find Nh4 (f3f4) with a score 100+
		//ProcessCommand("position r2r3k/p4Rp1/n2b3p/1p2p3/4P3/1BP1BN2/1PK2PPP/8 w - - 0 26"); 
		//ProcessCommand("go depth 9");

		//NewGame();

		//
		//ProcessCommand("position 8/2p1k3/1b3p2/3B4/2R2P2/6PK/7P/2r5 b - - 11 5"); 
		//ProcessCommand("go depth 18");

		//
		//ProcessCommand("position 4b3/2p1k3/5p2/3B4/2R2P2/6PK/7P/2r5 b - - 0 1"); 
		//ProcessCommand("go depth 8");

		//NewGame();

		// Needs to recognise that c2c1 is a 200+ score
		//ProcessCommand("position 2r2r1k/p2Qb1pp/8/4P3/1p3B2/6P1/P1q2PBP/2R3K1 b - - 4 29"); 
		//ProcessCommand("go wtime 60000 btime 60000 movestogo 10");
		//ProcessCommand("go wtime 4000 btime 4000 winc 1000 binc 1000");
		//ProcessCommand("go wtime 40000 btime 40000");
		//ProcessCommand("go depth 9");

		//ProcessCommand("position startpos moves d2d4 d7d5 c2c4 c7c6 g1f3 g8f6 b1c3 e7e6 e2e3 b8d7 f1d3 d5c4 d3c4 b7b5 c4d3 c8b7 e1g1 a7a6 e3e4 c6c5 d4d5 d8c7 d3c2 b5b4");
		//ProcessCommand("go wtime 72000 btime 69974 winc 1000 binc 1000");

		//ProcessCommand("position startpos moves e2e4 c7c5 g1f3 d7d6 d2d4 g8f6 b1c3 c5d4 f3d4 a7a6 f2f4 e7e5 d4f3 b8c6 f4e5 c6e5 c1e3 f6g4 e3d4 f8e7 h2h3 e7h4 e1e2 e5f3 g2f3 g4f6 h1g1 e8g8 e2d2 d8a5 d2c1 c8e6 f3f4 b7b5 c3b1 b5b4 f4f5 e6f5 e4f5 a5f5 b1d2 f8e8 f1d3 f5f4 d4b6 h4g3 d1f1 e8e1 f1e1 g3e1 g1e1 f4g3 e1e3 g3g1 d2f1 f6d5 e3e8 a8e8 b6g1 e8e1 c1d2 e1a1 g1h2 a1a2 d3c4 a2a5 h2d6 d5b6 c4d3 a5a2 d2c1 a2a1 c1d2 a6a5 f1e3 g7g6 d6c7 b6d7 d3b5 d7c5 b5c6 f7f5 c6d5 g8g7 c7e5 g7h6 b2b3 a1b1 e5c7 a5a4 c7d6 c5b3 c2b3 a4b3 d6b4 h6g5 d2c3 g5f4 e3g2 f4g3 h3h4 g3h3 b4e7 b3b2 e7a3 b1g1 a3b2 g1g2 d5g2 h3g2 b2c1 g2g3 c1g5 f5f4 c3d2 f4f3 d2e1 g3g2 g5e3 h7h6 e3f2 g6g5");
		//ProcessCommand("go movetime 2000");	

		// Endgame position - why does Rival want to sacrifice the white bishop by playing c4?
		//ProcessCommand("position 8/3k4/4R3/3Ppp2/8/1PP2P2/4r3/K2nB3 w - - 1 48"); 
		//ProcessCommand("go depth 10");	

		//ProcessCommand("position 2kr1bnr/pp4pp/2pq1p2/1N1ppb2/3P1B2/4P1P1/PPP1Qn1P/K3RBNR w - - 0 1"); 
		//ProcessCommand("go depth 12");

		// Time forfeit problem
		//ProcessCommand("position startpos moves e2e4 c7c5 g1f3 d7d6 f1b5 c8d7 b5d7 d8d7 e1g1 b8c6 c2c3 g8f6 d2d4 f6e4 d4d5 c6e5 f1e1 e5f3 d1f3 e4f6 c1g5 e8c8 g5f6 g7f6 f3h5 e7e6 b1d2 f8g7 d2e4 d7e7 a1d1 d8d7 e4g3 e7d8 d5e6 f7e6 e1e6 d8b6 g3e4 c8b8 e6d6 d7d6 d1d6 b6b2 h5d1 h8c8 d6d7 g7f8 e4f6 b2c3 f6h7 f8g7 h7g5 c3b2 g5e6 g7d4 g1h1 b2f2 e6d4 c5d4 d7d4 f2a2 h2h4 a7a5 d1e1 a2a3 e1e5 b8a7 d4d5 a3c1 h1h2 b7b6 d5d7 a7a6 e5f6 c8c7 d7d8 c7c6 f6e5 c6c5 e5e4 c1c2 d8a8 a6b5 e4e8 b5b4 a8b8 b6b5 e8e1 c2c3 e1b1 c3b3 b1e1 b4a4 b8d8 c5c2 e1a1 b3a3 a1d4 b5b4 d4d7 a4b3 d7f5 a3a2 d8d3 b3b2 h4h5 c2e2 f5g4 b2c1 g4g5 c1c2 d3d5 c2b3 h5h6 a2c2 d5a5 c2c7 h2h3 c7d7 h3h2 d7c7 h2h3 c7d7 a5f5 e2e6 g5g8 b3c2 h6h7 e6h6 h3g4 d7d1 g4f4 d1d4 f4g3 d4d6 f5f4 h6g6 g3h3 g6h6 h3g4 d6d1 g4g3 d1d3 g3g4 d3d1 g4f5 d1d3 f5g5 h6h7 g8a2 c2d1 a2a1 d1e2 a1f1 e2d2 f4f2 d2c3 f2f3 h7d7 f1c1 c3b3 f3d3 d7d3 c1c5 d3d2 c5e3 b3c2 e3e4 c2c3 e4c6 c3b2 c6f6 b2a2 f6a6 a2b2 a6f6 b2a2 g2g3 b4b3 f6c3 d2d5 g5g4 b3b2 c3c4 a2a1 c4a4 a1b1 a4e4 b1a1 e4a4 a1b1 g4h4 d5d2 a4e4 b1c1 e4c4 c1d1 c4f1 d1c2 f1c4 c2d1 c4e4 d1c1 e4c6 c1d1 c6h1 d1c2 h1c6 c2d1 c6b6 d1c1 b6g1 c1c2 g1c5 c2b3 c5f5 d2h2 h4g5 b3c3 f5c5 c3b3 c5e3 b3c2 e3e4 c2c1 e4e1 c1c2 e1e4 c2c1 e4f4 c1d1 f4d4 h2d2 d4e4 d1c1 e4c6 c1d1 c6e4 d1c1 e4c4 c1d1 c4a4 d1c1 a4c4 c1d1 c4b5 d2e2 g5f4 d1c1 b5c5 c1d1 c5g1 d1c2 g1c5 c2d1 c5d5 d1c1 d5c6 c1d1 c6d5 d1c1 d5c4 c1d1 c4d4 d1c1 d4c3 c1d1 c3d3 d1c1 d3c3 c1d1 c3d3 d1c1 d3c4 c1d1 c4b5 d1c1 b5e2 b2b1q e2e1 c1c2 e1e4 c2c1 e4e1 c1c2 e1e4 c2c1 e4e3 c1c2 e3e2 c2c1 e2e3 c1c2 e3f2 c2d3 f2f3 d3d4 f3e3 d4d5 e3e5 d5c6 e5e6 c6c7 e6e5 c7c6 e5e6 c6c7 e6f7 c7c6 f7c4 c6d7 ... c4d4");
		//ProcessCommand("go wtime 2786 btime 3349 winc 2000 binc 2000");

		// Lasker Position Kb1! instead of Kb2
		//ProcessCommand("position 8/k7/3p4/p2P1p2/P2P1P2/8/8/K7 w - - 0 1"); 
		//ProcessCommand("go depth 22");

		
		// Crash
		//ProcessCommand("position startpos moves e2e4 c7c5 g1f3 d7d6 d2d4 c5d4 f3d4 g8f6 b1c3 a7a6 a2a4 e7e6 f1e2 f8e7 e1g1 e8f8 d4f3 b8c6 c1g5 h7h6 g5f6 e7f6 d1d2 f6e7 e2c4 d8b6 b2b3 b6b4 d2d3 e7f6 c3a2 b4c5 c2c3 c6a5 a1b1 a5c4 d3c4 c5c4 b3c4 c8d7 b1b7 d7a4 b7b6 f8e7 b6b7 e7e8 f1e1 f6e7 a2b4 a6a5 e1a1 a4d7 e4e5 h6h5 g1h1 h5h4 a1d1 a5b4 e5d6 e7f6 c3b4 h4h3 b4b5 h3g2 h1g2 h8h5 d1e1 a8c8 b7c7 c8c7 d6c7 d7c8 b5b6 c8b7 e1d1 h5c5 d1c1 c5g5 g2f1 g5f5 f3e1 f6d4 f2f3 f5c5 e1d3 c5g5 d3f2 b7a6 c1b1 a6c4 f1e1 g5e5 f2e4 c4a6 b6b7 a6b7 b1b7 e8d7 e1f1 e5d5 c7c8n d7c8 b7f7 d5d7 f7f8 d7d8 f8d8 c8d8 f1e2 d8d7 e2d3 d4e5 h2h4 d7c6 d3c4 c6c7 h4h5 c7d7 e4f2 e5c7 f2g4 c7b6 c4d3 b6c5 g4e5 d7c7 d3e4 c7c8 f3f4 c8c7 e5g6 c7c6 g6e5 c6d6 e5d3 c5b6 d3e1 d6d7 e1d3 d7e8 d3e5 b6c5 e5g6 e8d8 e4e5 d8d7 e5e4 d7c7 e4e5 c7d8 e5e6 d8e8 f4f5 c5e3 f5f6 g7f6 e6f6 e3c1 g6e5 c1b2 f6f5 e8f8 e5c4 b2c3 h5h6 c3d4 f5g6 f8e7 h6h7 e7e6 c4e3 d4e5 e3f5 e5h8 f5g7 e6e7 g7f5"); 
		//ProcessCommand("go infinite");
		
		// Bc7 scores almost 200 - the black rook cannot defend the pawn due to back rank mate threat
		// after Nb6 drives the queen away from the back rank
		// 1.99 60703
		// Position 3
		ProcessCommand("position 1q2r2k/1p3ppp/pB6/P2NpPb1/4P3/1N6/1PQ3PP/5K2 w - - 1 27"); 
		ProcessCommand("go depth 10");
	
		// 25.6 51172
		// Position 2
		//ProcessCommand("position 8/5k2/5pp1/5p1p/5P1P/6r1/4K3/8 b - - 1 72"); 
		//ProcessCommand("go depth 20");

		// Bxf1 is a blunder
		// 7.8 26094
		// Position 1
		//ProcessCommand("position 1qr3rk/1p2bppp/pB6/Pb1NpP2/4P3/1N6/1Pn3PP/2RQ1RK1 b - - 2 23"); 
		//ProcessCommand("go depth 8");

	}
}

int main(int argc, char *args[])
{
#ifdef NORANDOM
	srand(1);
#else
	srand((unsigned)time(0));
#endif

	//ClearLog();

	//PrepareOpenings();

#ifdef TESTING
	ProcessCommand("uci");
	ProcessCommand("setoption name Hash value 64");
	ProcessCommand("isready");
	ProcessCommand("stop");
	ProcessCommand("ucinewgame");
	Test();
#else
	LoopForCommandsAndProcess();
#endif
	if (Searcher)
	{
		delete Searcher;
	}
	if (Game)
	{
		delete Game;
	}
	DeleteOpeningPositions();
}
