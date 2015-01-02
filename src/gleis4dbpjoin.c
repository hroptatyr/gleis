/*** gleis4dbpjoin.c -- c-lei file parser
 *
 * Copyright (C) 2014-2015  Sebastian Freundt
 *
 * Author:  Sebastian Freundt <freundt@ga-group.nl>
 *
 * This file is part of gleis.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * 3. Neither the name of the author nor the names of any contributors
 *    may be used to endorse or promote products derived from this
 *    software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
 * BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE
 * OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN
 * IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 **/
#if defined HAVE_CONFIG_H
# include "config.h"
#endif	/* HAVE_CONFIG_H */
#include <unistd.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>
#if defined __INTEL_COMPILER
# pragma warning (disable:1292)
#endif  /* __INTEL_COMPILER */
#include <libxml/parser.h>
#if defined __INTEL_COMPILER
# pragma warning (default:1292)
#endif  /* __INTEL_COMPILER */

#if !defined UNUSED
# define UNUSED(_x)	__attribute__((unused)) _x##_unused
#endif  /* !UNUSED */
#if !defined LIKELY
# define LIKELY(_x)	__builtin_expect((_x), 1)
#endif
#if !defined UNLIKELY
# define UNLIKELY(_x)	__builtin_expect((_x), 0)
#endif
#define countof(_x)	(sizeof(_x) / sizeof(*_x))

struct lei_s {
	size_t lei;
	size_t llen;
	size_t name;
	size_t nlen;
	size_t webs;
	size_t wlen;
};


/* aux stuff */
static const char*
tag_massage(const char *tag)
{
/* return the real part of a (ns'd) tag or attribute,
 * i.e. foo:that_tag becomes that_tag */
	const char *p = strchr(tag, ':');

	if (p) {
		/* skip over ':' */
		return p + 1;
	}
	/* otherwise just return the tag as is */
	return tag;
}


/* temporary buffer */
static char *sbuf;
static size_t sbix;
static size_t sbsz;

/* output buffer */
static char *obuf;
static size_t obix;
static size_t obsz;

static int
sax_buf_resz(size_t len)
{
	if (UNLIKELY(sbix + len >= sbsz)) {
		size_t new_sz = sbix + len + 1U;

		/* round to multiple of 4096 */
		sbsz = (new_sz & ~0xfff) + 4096L;
		/* realloc now */
		if (UNLIKELY((sbuf = realloc(sbuf, sbsz)) == NULL)) {
			return -1;
		}
	}
	return 0;
}

static ssize_t
sax_buf_push(const char *txt, size_t len)
{
	/* resize? */
	if (UNLIKELY(sax_buf_resz(len) < 0)) {
		return -1;
	}
	/* now copy */
	memcpy(sbuf + sbix, txt, len);
	sbuf[sbix += len] = '\0';
	return len;
}

static size_t
sax_buf_massage(size_t from)
{
	size_t i;
	size_t o;
	const char *tp;

	if (LIKELY((tp = strchr(sbuf + from, '&')) == NULL)) {
		/* nothing to do */
		return sbix;
	}
	/* otherwise head-start on the copy-and-decode loop */
	for (i = o = tp - sbuf; i < sbix; i++, o++) {
		if ((sbuf[o] = sbuf[i]) == '&') {
			if (0) {
				;
			} else if (!memcmp(sbuf + i, "&amp;", 5U)) {
				sbuf[o] = '&';
				i += 4U;
			} else if (!memcmp(sbuf + i, "&lt;", 4U)) {
				sbuf[o] = '<';
				i += 3U;
			} else if (!memcmp(sbuf + i, "&gt;", 4U)) {
				sbuf[o] = '>';
				i += 3U;
			} else if (!memcmp(sbuf + i, "&quot;", 6U)) {
				sbuf[o] = '"';
				i += 5U;
			} else if (!memcmp(sbuf + i, "&apos;", 6U)) {
				sbuf[o] = '\'';
				i += 5U;
			}
		}
	}
	sbuf[sbix = o] = '\0';
	return sbix;
}

static void
sax_buf_reset(void)
{
	sbix = 0U;
	return;
}

static int
out_buf_flsh(size_t len)
{
#define FORCE_FLUSH	((size_t)-1)
	if (UNLIKELY(len == FORCE_FLUSH)) {
		/* definitely flush */
		;
	} else if (LIKELY(obix + len <= obsz)) {
		/* no flush */
		return 0;
	} else if (UNLIKELY(!obix)) {
		return 0;
	}
	for (ssize_t nwr, tot = 0U; (size_t)tot < obix; tot += nwr) {
		nwr = write(STDOUT_FILENO, obuf + tot, obix - tot);
		if (UNLIKELY(nwr < 0)) {
			return -1;
		}
	}
	obix = 0U;
	return 0;
}

static int
out_buf_resz(size_t len)
{
	if (UNLIKELY(len > obsz)) {
		/* resize */
		size_t new_sz = len;

		/* round to multiple of 4096 */
		obsz = (new_sz & ~0xfff) + 4096L;
		/* realloc now */
		if (UNLIKELY((obuf = realloc(obuf, obsz)) == NULL)) {
			return -1;
		}
	}
	return 0;
}

static int
out_buf_push(const char *str, size_t len)
{
	/* flush? */
	if (UNLIKELY(out_buf_flsh(len + 1U) < 0)) {
		return -1;
	}
	/* resize? */
	if (UNLIKELY(out_buf_resz(len + 1U) < 0)) {
		return -1;
	}
	/* now copy */
	memcpy(obuf + obix, str, len);
	obuf[obix += len] = '\0';
	return 0;
}

static int
out_buf_push_nws(const char *str, size_t len)
{
/* like out_buf_push() but also normalise whitespace */
	size_t i = 0U;
	size_t clen = 0U;

	/* flush? */
	if (UNLIKELY(out_buf_flsh(len + 1U)) < 0) {
		return -1;
	}
	/* resize? */
	if (UNLIKELY(out_buf_resz(len + 1U) < 0)) {
		return -1;
	}
	/* skip leading ws */
	for (i = 0U; i < len; i++) {
		switch (str[i]) {
		case ' ':
		case '\t':
		case '\n':
		case '\f':
			continue;
		default:
			break;
		}
		break;
	}
	/* now esc-copy */
	for (; i < len; i++) {
		switch (str[i]) {
		default:
			obuf[obix + clen++] = str[i];
			break;
		case ' ':
		case '\t':
		case '\n':
		case '\f':
			obuf[obix + clen++] = ' ';
			break;
		}
	}
	/* kill trailing ws */
	for (; i > 0; i--) {
		switch (str[i - 1]) {
		case ' ':
		case '\t':
		case '\n':
		case '\f':
			continue;
		default:
			break;
		}
		break;
	}
	/* perfect */
	obuf[obix += clen] = '\0';
	return 0;
}


/* our SAX parser */
static bool pushp;
static bool in_ent_p;
static enum {
	FL_UNK,
	FL_CLEIS,
	FL_PLEIS,
} flavour;

static xmlEntityPtr
sax_get_ent(void *UNUSED(ctx), const xmlChar *name)
{
	return xmlGetPredefinedEntity(name);
}

static void
sax_text(void *UNUSED(ctx), const xmlChar *txt, int len)
{
	if (pushp) {
		sax_buf_push((const char*)txt, (size_t)len);
	}
	return;
}

static void
sax_bo(void *ctx, const xmlChar *name, const xmlChar **atts)
{
	/* where the real element name starts, sans ns prefix */
	const char *rname = tag_massage((const char*)name);
	struct lei_s *r = ctx;

	switch (flavour) {
	case FL_UNK:
		if (!strcmp(rname, "LEIRecords")) {
			flavour = FL_CLEIS;
		} else if (!strcmp(rname, "LEIRegistrations")) {
			flavour = FL_PLEIS;
		} else {
			break;
		}
		break;

	case FL_CLEIS:
		if (in_ent_p) {
			if (!strcmp(rname, "LegalName")) {
				r->name = sbix;
				pushp = true;
			}
		} else if (!strcmp(rname, "Entity")) {
			in_ent_p = true;
		} else if (!strcmp(rname, "LEI")) {
			r->lei = sbix;
			pushp = true;
		}
		break;

	case FL_PLEIS:
		if (!strcmp(rname, "LegalEntityIdentifier")) {
			r->lei = sbix;
			pushp = true;
		} else if (!strcmp(rname, "RegisteredName")) {
			r->name = sbix;
			pushp = true;
		} else if (!strcmp(rname, "EntityWebsiteAddress")) {
			r->webs = sbix;
			pushp = true;
		}
		break;

	default:
		break;
	}
	return;
}

static void
sax_eo(void *ctx, const xmlChar *name)
{
	/* where the real element name starts, sans ns prefix */
	const char *rname = tag_massage((const char*)name);
	struct lei_s *r = ctx;

	switch (flavour) {
	case FL_UNK:
		break;

	case FL_CLEIS:
		if (in_ent_p) {
			if (0) {
				;
			} else if (!strcmp(rname, "LegalName")) {
				r->nlen = sbix - r->name;
			} else if (!strcmp(rname, "Entity")) {
				in_ent_p = false;
			}
			pushp = false;
		} else if (!strcmp(rname, "LEI")) {
			r->llen = sbix - r->lei;
			pushp = false;
		} else if (!strcmp(rname, "LEIRecord")) {
			if (r->llen && r->nlen) {
				goto print;
			}
			goto reset;
		} else if (!strcmp(rname, "LEIRecords")) {
			goto final;
		}
		break;

	case FL_PLEIS:
		if (!strcmp(rname, "LegalEntityIdentifier")) {
			r->llen = sax_buf_massage(r->lei) - r->lei;
			pushp = false;
		} else if (!strcmp(rname, "RegisteredName")) {
			r->nlen = sax_buf_massage(r->name) - r->name;
			pushp = false;
		} else if (!strcmp(rname, "EntityWebsiteAddress")) {
			r->wlen = sax_buf_massage(r->webs) - r->webs;
			pushp = false;
		} else if (!strcmp(rname, "LEIRegistration")) {
			if (r->llen && r->nlen) {
				goto print;
			}
			goto reset;
		} else if (!strcmp(rname, "LEIRegistrations")) {
			goto final;
		}
		break;

	default:
		break;

	print:
		/* principal type info */
		out_buf_push("ol:", 3U);
		out_buf_push(sbuf + r->lei, r->llen);
		out_buf_push("\t", 1U);
		out_buf_push_nws(sbuf + r->name, r->nlen);
		if (r->wlen) {
			out_buf_push("\t", 1U);
			out_buf_push_nws(sbuf + r->webs, r->wlen);
		}
		out_buf_push("\n", 1U);

	reset:
		memset(r, 0, sizeof(*r));
		sax_buf_reset();
		break;

	final:
		/* flush buffer */
		out_buf_flsh(FORCE_FLUSH);
		flavour = FL_UNK;
		in_ent_p = false;
		pushp = false;
		goto reset;
	}
	return;
}


static xmlSAXHandler hdl = {
	.characters = sax_text,
	.getEntity = sax_get_ent,
	.startElement = sax_bo,
	.endElement = sax_eo,
};

static int
_parse(const char *file)
{
	static struct lei_s r[1U];
	int rc;

	rc = xmlSAXUserParseFile(&hdl, r, file ?: "-");

	/* free resources */
	if (LIKELY(sbuf != NULL)) {
		free(sbuf);
		sbuf = NULL;
		sbix = 0U;
		sbsz = 0U;
	}
	if (LIKELY(obuf != NULL)) {
		free(obuf);
		obuf = NULL;
		obix = 0U;
		obsz = 0U;
	}
	return rc;
}


#include "gleis4dbpjoin.yucc"

int
main(int argc, char *argv[])
{
	yuck_t argi[1U];
	size_t i;
	int rc;

	if (yuck_parse(argi, argc, argv) < 0) {
		rc = 1;
		goto out;
	}

	/* assume success */
	rc = 0;

	/* check if no files have been supplied */
	i = 0U;
	if (!argi->nargs) {
		/* read stdin */
		goto one_off;
	}
	for (; i < argi->nargs; i++) {
	one_off:
		if (_parse(argi->args[i]) != 0) {
			fprintf(stderr, "\
gleis4dbpjoin: Error: cannot convert `%s'\n", argi->args[i]);
			rc++;
		}
	}

out:
	yuck_free(argi);
	return rc;
}

/* gleis4dbpjoin.c ends here */
