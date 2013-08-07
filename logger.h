#ifndef _LOGGER_H
#define _LOGGER_H

#include <fstream>
#include <iostream>

using namespace std;

#define LOG_FILE "c:\\log.txt"
#define LOG_ENDL "\r\n"
#define LOGTEXTSIZE 1000

void ClearLog();
void WriteLog(char* s, char* a);
void WriteLog(char* s);

#endif

