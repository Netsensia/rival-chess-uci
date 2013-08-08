#pragma unmanaged

#include "logger.h"

void ClearLog()
{
	FILE* f;
	fopen_s(&f, LOG_FILE, "w");
	fclose(f);
}

void WriteLog(char* s, char* a)
{
	std::ofstream out(LOG_FILE, ios_base::app);
	out << a << s << LOG_ENDL;
	out.close();
}

void WriteLog(char* s)
{
	char p[LOGTEXTSIZE];
	sprintf_s(p, "%s", s);
	WriteLog(p, "Debug:");
}
