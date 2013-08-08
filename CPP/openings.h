#include "chessbrd.h"

#ifndef _OPENINGS_H
#define _OPENINGS_H

bool GetOpening(TChessBoard* Game, TMove& Move);
void CacheOpenings(char* filename);
void DeleteOpeningPositions();

#endif

