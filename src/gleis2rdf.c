/*** gleis2rdf.c -- c-lei file parser
 *
 * Copyright (C) 2014-2018  Sebastian Freundt
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
#define strlenof(_x)	(sizeof(_x) - 1U)

#if defined __GLIBC__ && __GLIBC__ >= 2
# define fputc	fputc_unlocked
# define fwrite	fwrite_unlocked
#endif

struct lei_s {
	off_t lei;
	size_t llen;
	off_t name;
	size_t nlen;
	off_t form;
	size_t flen;
	off_t fcod;
	size_t clen;
	off_t ofrm;
	size_t olen;
	off_t jrsd;
	size_t jlen;
	off_t stat;
	size_t slen;
	char lang[8U];
	off_t date;
	size_t dlen;
	off_t irdate;
	size_t irdlen;
	off_t ludate;
	size_t ludlen;
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

static inline __attribute__((unused, pure, const)) char
c2h(int x)
{
	const unsigned char y = (unsigned char)(x & 0b1111U);
	if (y < 10) {
		return (char)(y ^ '0');
	}
	return (char)(y + '7');
}


/* temporary buffer */
static char *sbuf;
static size_t sbix;
static size_t sbsz;

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
out_buf_push(const char *str, size_t len)
{
	fwrite(str, sizeof(*str), len, stdout);
	return 0;
}

static int
out_buf_push_esc(const char *str, size_t len)
{
/* like out_buf_push() but account for the necessity that we have
 * to escape every character */
	/* now esc-copy */
	for (size_t i = 0U; i < len; i++) {
		switch (str[i]) {
		case '"':
		case '\n':
		case '\\':
			fputc('\\', stdout);
		default:
			fputc(str[i], stdout);
			break;
		}
	}
	return 0;
}

static int
out_buf_push_iri(const char *str, size_t len)
{
/* like out_buf_push() but % escape things */
	/* now esc-copy */
	for (size_t i = 0U; i < len; i++) {
		switch (str[i]) {
		case '>':
			fwrite("\\u003E", sizeof(char), 6U, stdout);
			break;
		case '<':
			fwrite("\\u003C", sizeof(char), 6U, stdout);
			break;
		case '"':
			fwrite("\\u0022", sizeof(char), 6U, stdout);
			break;
		case '\n':
			fwrite("\\u000A", sizeof(char), 6U, stdout);
			break;
		default:
			fputc(str[i], stdout);
			break;
		}
	}
	return 0;
}

static int
out_buf_push_esc_nws(const char *str, size_t len)
{
/* like out_buf_push_esc() but also normalise whitespace */
	size_t i = 0U;

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
		case ' ':
		case '\t':
		case '\n':
		case '\f':
			fputc(' ', stdout);
			break;
		case '"':
		case '\\':
			fputc('\\', stdout);
		default:
			fputc(str[i], stdout);
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
	return 0;
}


/* our SAX parser */
static bool pushp;
static bool in_ent_p;
static bool in_reg_p;
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
		static const char pre[] = "\
@prefix lei: <http://openleis.com/legal_entities/> .\n\
@prefix leiroc: <http://www.leiroc.org/data/schema/leidata/2014/> .\n\
@prefix fibo-be-le-lei: <http://www.omg.org/spec/EDMC-FIBO/BE/LegalEntities/LEIEntities/> .\n\
@prefix rov: <http://www.w3.org/ns/regorg#> .\n\
@prefix gas: <http://schema.ga-group.nl/symbology#> .\n\
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n\
\n";

	case FL_UNK:
		if (!strcmp(rname, "LEIRecords")) {
			flavour = FL_CLEIS;
		} else if (!strcmp(rname, "LEIRegistrations")) {
			flavour = FL_PLEIS;
		} else if (!strcmp((const char*)name, "lei:ContentDate")) {
			r->date = sbix;
			pushp = true;
			break;
		} else {
			break;
		}
		out_buf_push(pre, strlenof(pre));

		if (r->dlen) {
			static const char tpre[] = "\
@prefix TIME: <", post[] = "> .\n";
			out_buf_push(tpre, strlenof(tpre));
			out_buf_push(sbuf + r->date, r->dlen);
			out_buf_push(post, strlenof(post));
		}
		break;

	case FL_CLEIS:
		if (in_ent_p) {
			if (0) {
				;
			} else if (!strcmp(rname, "LegalName")) {
				r->name = sbix;
				pushp = true;
				if (atts) {
					/* snarf language tag */
					goto lang;
				}
			} else if (!strcmp(rname, "LegalForm")) {
				r->form = sbix;
				pushp = true;
			} else if (!strcmp(rname, "EntityLegalFormCode")) {
				r->fcod = sbix;
				pushp = true;
			} else if (!strcmp(rname, "OtherLegalForm")) {
				r->ofrm = sbix;
				pushp = true;
			} else if (!strcmp(rname, "LegalJurisdiction")) {
				r->jrsd = sbix;
				pushp = true;
			} else if (!strcmp(rname, "EntityStatus")) {
				r->stat = sbix;
				pushp = true;
			}
		} else if (in_reg_p) {
			if (0) {
				;
			} else if (!strcmp(rname, "InitialRegistrationDate")) {
				r->irdate = sbix;
				pushp = true;
			} else if (!strcmp(rname, "LastUpdateDate")) {
				r->ludate = sbix;
				pushp = true;
			}
		} else if (!strcmp(rname, "Entity")) {
			in_ent_p = true;
		} else if (!strcmp(rname, "Registration")) {
			in_reg_p = true;
		} else if (!strcmp(rname, "LEI")) {
			r->lei = sbix;
			pushp = true;
		}
		break;
	lang:
		for (const xmlChar **a = atts; *a; a++) {
			const char *aname = tag_massage((const char*)*a++);
			if (!strcmp(aname, "lang")) {
				const char *lang = (const char*)*a;
				const size_t llen = strlen(lang);
				memcpy(r->lang, lang, llen < 7U ? llen : 7U);
			}
		}
		break;

	case FL_PLEIS:
		if (!strcmp(rname, "LegalEntityIdentifier")) {
			r->lei = sbix;
			pushp = true;
		} else if (!strcmp(rname, "RegisteredName")) {
			r->name = sbix;
			pushp = true;
		} else if (!strcmp(rname, "EntityLegalForm")) {
			r->form = sbix;
			pushp = true;
		} else if (!strcmp(rname, "RegisteredCountryCode")) {
			r->jrsd = sbix;
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
		if (!strcmp((const char*)name, "lei:ContentDate")) {
			r->dlen = sbix - r->date;
		}
		pushp = false;
		break;

	case FL_CLEIS:
		if (in_ent_p) {
			if (0) {
				;
			} else if (!strcmp(rname, "LegalName")) {
				r->nlen = sbix - r->name;
			} else if (!strcmp(rname, "LegalForm")) {
				r->flen = sbix - r->form;
			} else if (!strcmp(rname, "OtherLegalForm")) {
				r->olen = sbix - r->ofrm;
			} else if (!strcmp(rname, "EntityLegalFormCode")) {
				r->clen = sbix - r->fcod;
			} else if (!strcmp(rname, "LegalJurisdiction")) {
				r->jlen = sbix - r->jrsd;
			} else if (!strcmp(rname, "EntityStatus")) {
				r->slen = sbix - r->stat;
			} else if (!strcmp(rname, "Entity")) {
				in_ent_p = false;
			}
		} else if (in_reg_p) {
			if (0) {
				;
			} else if (!strcmp(rname, "InitialRegistrationDate")) {
				r->irdlen = sbix - r->irdate;
			} else if (!strcmp(rname, "LastUpdateDate")) {
				r->ludlen = sbix - r->ludate;
			} else if (!strcmp(rname, "Registration")) {
				in_reg_p = false;
			}
		} else if (!strcmp(rname, "LEI")) {
			r->llen = sbix - r->lei;
		} else if (!strcmp(rname, "LEIRecord")) {
			if (r->llen) {
				goto print;
			}
			goto reset;
		} else if (!strcmp(rname, "LEIRecords")) {
			goto final;
		}
		pushp = false;
		break;

	case FL_PLEIS:
		if (!strcmp(rname, "LegalEntityIdentifier")) {
			r->llen = sax_buf_massage(r->lei) - r->lei;
		} else if (!strcmp(rname, "RegisteredName")) {
			r->nlen = sax_buf_massage(r->name) - r->name;
		} else if (!strcmp(rname, "EntityLegalForm")) {
			r->flen = sax_buf_massage(r->form) - r->form;
		} else if (!strcmp(rname, "RegisteredCountryCode")) {
			r->jlen = sax_buf_massage(r->jrsd) - r->jrsd;
		} else if (!strcmp(rname, "LEIRegistration")) {
			if (r->llen) {
				goto print;
			}
			goto reset;
		} else if (!strcmp(rname, "LEIRegistrations")) {
			goto final;
		}
		pushp = false;
		break;

	default:
		break;

	print:
		/* provenance service */
		if (r->ludlen) {
			static const char pre[] = "\
@prefix MODD: <", post[] = "> .\n";

			out_buf_push(pre, strlenof(pre));
			out_buf_push(sbuf + r->ludate, r->ludlen);
			out_buf_push(post, strlenof(post));
		}
		/* principal type info */
		out_buf_push("lei:", 4U);
		out_buf_push(sbuf + r->lei, r->llen);
		out_buf_push(" a leiroc:LEI ", 14U);

		static const char lei[] =
			", fibo-be-le-lei:LegalEntityIdentifier ";
		static const char cce[] =
			", fibo-be-le-lei:ContractuallyCapableEntity ";
		out_buf_push(lei, strlenof(lei));
		out_buf_push(cce, strlenof(cce));

		static const char sof[] =
			";\n   gas:symbolOf <http://openleis.com/> ";

		out_buf_push(sof, strlenof(sof));

		if (r->nlen) {
			static const char tag[] = "leiroc:LegalName";
			
			out_buf_push(";\n   ", 5U);
			out_buf_push(tag, strlenof(tag));
			out_buf_push(" \"\"\"", 4U);
			out_buf_push_esc_nws(sbuf + r->name, r->nlen);
			if (!*r->lang) {
				out_buf_push("\"\"\" ", 4U);
			} else {
				out_buf_push("\"\"\"@", 4U);
				out_buf_push(r->lang, strlen(r->lang));
			}
		}
		if (r->irdlen) {
			static const char tag[] = "leiroc:InitialRegistrationDate";
			out_buf_push(";\n   ", 5U);
			out_buf_push(tag, strlenof(tag));
			out_buf_push(" \"", 2U);
			out_buf_push(sbuf + r->irdate, r->irdlen);
			out_buf_push("\"^^xsd:dateTime ", 16U);
		}
		if (r->ludlen) {
			static const char tag[] = "leiroc:LastUpdateDate";
			out_buf_push(";\n   ", 5U);
			out_buf_push(tag, strlenof(tag));
			out_buf_push(" \"", 2U);
			out_buf_push(sbuf + r->ludate, r->ludlen);
			out_buf_push("\"^^xsd:dateTime ", 16U);
		}
		if (r->clen && sbuf[r->fcod] != '<') {
			/* append legal form */
			static const char tag[] = "leiroc:EntityLegalFormCode";

			out_buf_push(";\n   ", 5U);
			out_buf_push(tag, strlenof(tag));
			out_buf_push(" \"", 2U);
			out_buf_push_esc(sbuf + r->fcod, r->clen);
			out_buf_push("\" ", 2U);
		}
		if (r->olen && sbuf[r->ofrm] != '<') {
			/* append legal form */
			static const char tag[] = "leiroc:LegalForm";
			static const char typ[] = "rov:orgType";
			static const char fpre[] = "http://openleis.com/legal_entities/search/legal_form/";

			out_buf_push(";\n   ", 5U);
			out_buf_push(tag, strlenof(tag));
			out_buf_push(" \"\"\"", 4U);
			out_buf_push_esc(sbuf + r->ofrm, r->olen);
			out_buf_push("\"\"\" ", 4U);

			/* and as rov:orgType */
			out_buf_push(";\n   ", 5U);
			out_buf_push(typ, strlenof(typ));
			out_buf_push(" <", 2U);
			out_buf_push(fpre, strlenof(fpre));
			out_buf_push_iri(sbuf + r->ofrm, r->olen);
			out_buf_push("> ", 2U);
		}
		if (r->flen && !(r->olen || r->clen) && sbuf[r->form] != '<') {
			/* append legal form */
			static const char tag[] = "leiroc:LegalForm";
			static const char typ[] = "rov:orgType";
			static const char fpre[] = "http://openleis.com/legal_entities/search/legal_form/";

			out_buf_push(";\n   ", 5U);
			out_buf_push(tag, strlenof(tag));
			out_buf_push(" \"\"\"", 4U);
			out_buf_push_esc(sbuf + r->form, r->flen);
			out_buf_push("\"\"\" ", 4U);

			/* and as rov:orgType */
			out_buf_push(";\n   ", 5U);
			out_buf_push(typ, strlenof(typ));
			out_buf_push(" <", 2U);
			out_buf_push(fpre, strlenof(fpre));
			out_buf_push_iri(sbuf + r->form, r->flen);
			out_buf_push("> ", 2U);
		}
		if (r->jlen) {
			/* append legal form */
			static const char tag[] = "leiroc:LegalJurisdiction";
			static const char jur[] = "http://schema.ga-group.nl/jurisdictions#";

			out_buf_push(";\n   ", 5U);
			out_buf_push(tag, strlenof(tag));
			out_buf_push(" \"\"\"", 4U);
			out_buf_push_esc(sbuf + r->jrsd, r->jlen);
			out_buf_push("\"\"\" ", 4U);

			/* and again as fibo-be-le-lei statement */
			out_buf_push(";\n   ", 5U);
			out_buf_push("fibo-be-le-lei:isRecognizedIn", 29U);
			out_buf_push(" <", 2U);
			out_buf_push(jur, strlenof(jur));
			out_buf_push_iri(sbuf + r->jrsd, r->jlen);
			out_buf_push("> ", 2U);
		}

		if (r->slen) {
			/* append status */
			static const char tag[] = "rov:orgStatus";
			out_buf_push(";\n   ", 5U);
			out_buf_push(tag, strlenof(tag));
			out_buf_push(" \"", 2U);
			out_buf_push(sbuf + r->stat, r->slen);
			out_buf_push("\" ", 2U);
		}

		out_buf_push(".\n", 2U);

	reset:
		memset(r, 0, sizeof(*r));
		sax_buf_reset();
		break;

	final:
		/* flush buffer */
		fflush(stdout);
		flavour = FL_UNK;
		in_ent_p = false;
		in_reg_p = false;
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
	return rc;
}


#include "gleis2rdf.yucc"

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
gleis2rdf: Error: cannot convert `%s'\n", argi->args[i]);
			rc++;
		}
	}

out:
	yuck_free(argi);
	return rc;
}

/* gleis2rdf.c ends here */
