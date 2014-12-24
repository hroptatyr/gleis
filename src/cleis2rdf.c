/*** cleis2rdf.c -- c-lei file parser
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
	size_t form;
	size_t flen;
	size_t jrsd;
	size_t jlen;
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
	if (UNLIKELY(out_buf_flsh(len) < 0)) {
		return -1;
	}
	/* resize? */
	if (UNLIKELY(out_buf_resz(len) < 0)) {
		return -1;
	}
	/* now copy */
	memcpy(obuf + obix, str, len);
	obuf[obix += len] = '\0';
	return 0;
}

static int
out_buf_push_esc(const char *str, size_t len)
{
/* like out_buf_push() but account for the necessity that we have
 * to escape every character */
	size_t clen = 0U;

	/* flush? */
	if (UNLIKELY(out_buf_flsh(2U * len)) < 0) {
		return -1;
	}
	/* resize? */
	if (UNLIKELY(out_buf_resz(2U * len) < 0)) {
		return -1;
	}
	/* now esc-copy */
	for (size_t i = 0U; i < len; i++) {
		switch (str[i]) {
		default:
			obuf[obix + clen++] = str[i];
			break;
		case '"':
		case '\n':
		case '\\':
			obuf[obix + clen++] = '\\';
			obuf[obix + clen++] = str[i];
			break;
		}
	}
	obuf[obix += clen] = '\0';
	return 0;
}

static int
out_buf_push_esc_nws(const char *str, size_t len)
{
/* like out_buf_push_esc() but also normalise whitespace */
	size_t i = 0U;
	size_t clen = 0U;

	/* flush? */
	if (UNLIKELY(out_buf_flsh(2U * len)) < 0) {
		return -1;
	}
	/* resize? */
	if (UNLIKELY(out_buf_resz(2U * len) < 0)) {
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
		case '"':
		case '\\':
			obuf[obix + clen++] = '\\';
			obuf[obix + clen++] = str[i];
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

	if (0) {
		;
	} else if (in_ent_p) {
		if (0) {
			;
		} else if (!strcmp(rname, "LegalName")) {
			r->name = sbix;
			pushp = true;
		} else if (!strcmp(rname, "LegalForm")) {
			r->form = sbix;
			pushp = true;
		} else if (!strcmp(rname, "LegalJurisdiction")) {
			r->jrsd = sbix;
			pushp = true;
		}
	} else if (!strcmp(rname, "Entity")) {
		in_ent_p = true;
	} else if (!strcmp(rname, "LEI")) {
		r->lei = sbix;
		pushp = true;
	} else if (!strcmp(rname, "LEIRecords")) {
		static const char pre[] = "\
@prefix ol: <http://openleis.com/legal_entities/> .\n\
@prefix lei: <http://www.leiroc.org/data/schema/leidata/2014/> .\n\
\n";
		out_buf_push(pre, sizeof(pre) - 1U);
	}
	return;
}

static void
sax_eo(void *ctx, const xmlChar *name)
{
	/* where the real element name starts, sans ns prefix */
	const char *rname = tag_massage((const char*)name);
	struct lei_s *r = ctx;

	if (0) {
		;
	} else if (in_ent_p) {
		if (0) {
			;
		} else if (!strcmp(rname, "LegalName")) {
			r->nlen = sbix - r->name;
		} else if (!strcmp(rname, "LegalForm")) {
			r->flen = sbix - r->form;
		} else if (!strcmp(rname, "LegalJurisdiction")) {
			r->jlen = sbix - r->jrsd;
		} else if (!strcmp(rname, "Entity")) {
			in_ent_p = false;
		}
		pushp = false;
	} else if (!strcmp(rname, "LEI")) {
		r->llen = sbix - r->lei;
		pushp = false;
	} else if (!strcmp(rname, "LEIRecord")) {
		if (r->llen && r->nlen) {
			static const char ltag[] = "lei:LegalName";
			
			out_buf_push("ol:", 3U);
			out_buf_push(sbuf + r->lei, r->llen);

			out_buf_push(" ", 1U);
			out_buf_push(ltag, sizeof(ltag) - 1U);
			out_buf_push(" \"", 2U);
			out_buf_push_esc_nws(sbuf + r->name, r->nlen);
			out_buf_push("\" ", 2U);

			if (r->flen) {
				/* append legal form */
				static const char tag[] = "lei:LegalForm";

				out_buf_push(";\n   ", 5U);
				out_buf_push(tag, sizeof(tag) - 1U);
				out_buf_push(" \"", 2U);
				out_buf_push_esc(sbuf + r->form, r->flen);
				out_buf_push("\" ", 2U);
			}
			if (r->jlen) {
				/* append legal form */
				static const char tag[] = "lei:LegalJurisdiction";
				out_buf_push(";\n   ", 5U);
				out_buf_push(tag, sizeof(tag) - 1U);
				out_buf_push(" \"", 2U);
				out_buf_push_esc(sbuf + r->jrsd, r->jlen);
				out_buf_push("\" ", 2U);
			}
			out_buf_push(".\n", 2U);
		}
		memset(r, 0, sizeof(*r));
		sax_buf_reset();
	} else if (!strcmp(rname, "LEIRecords")) {
		/* flush buffer */
		out_buf_flsh(FORCE_FLUSH);
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

	rc = xmlSAXUserParseFile(&hdl, r, file);

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


int
main(int argc, char *argv[])
{
	return !!_parse(argv[1U]);
}

/* cleis2rdf.c ends here */
