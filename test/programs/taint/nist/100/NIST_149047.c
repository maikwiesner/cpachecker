/*PLOVER: BUFF.OVER, BUFF.FORMAT*/

/*
Description: Syslog is called with a user supplied format string.
Keywords: Size0 Complex0 Taint FormatString
ValidArg: "'NormalString\n'"
InvalidArg: "%s"*100
*/

// This file is part of the SV-Benchmarks collection of verification tasks:
// https://github.com/sosy-lab/sv-benchmarks
//
// SPDX-FileCopyrightText: 2010-2021 NIST
// SPDX-FileCopyrightText: 2021 The SV-Benchmarks Community
//
// SPDX-License-Identifier: CC0-1.0

#include <syslog.h>
#include <string.h>

void
filter(char *str, const char *whitelist)
{
	char *src, *dst;
	for(src = str, dst = str; *src; src++)
		if(strchr(whitelist, *src) != NULL)
			*dst++ = *src;
	*dst = '\0';
}

void
test(char *str)
{
	filter(str, "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789: %");
	syslog(LOG_CRIT, str);			/* FLAW */
}

int
main(int argc, char **argv)
{
	char *userstr;

	if(argc > 1) {
		userstr = argv[1];
		test(userstr);
	}
	return 0;
}
