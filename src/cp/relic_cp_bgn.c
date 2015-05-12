/*
 * RELIC is an Efficient LIbrary for Cryptography
 * Copyright (C) 2007-2015 RELIC Authors
 *
 * This file is part of RELIC. RELIC is legal property of its developers,
 * whose names are not listed here. Please refer to the COPYRIGHT file
 * for contact information.
 *
 * RELIC is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * RELIC is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with RELIC. If not, see <http://www.gnu.org/licenses/>.
 */

/**
 * @file
 *
 * Implementation of Freeman's prime-order version of the Boneh-Goh-Nissim
 * cryptosystem.
 *
 * @version $Id$
 * @ingroup cp
 */

#include <limits.h>

#include "relic_core.h"
#include "relic_conf.h"
#include "relic_rand.h"
#include "relic_bn.h"
#include "relic_util.h"
#include "relic_cp.h"
#include "relic_md.h"

#define LUT 1

/*============================================================================*/
/* HASHTABLE			                                                         */
/*============================================================================*/
#ifdef LUT
	struct nlist { /* table entry: */
	    struct nlist *next; /* next entry in chain */
	    uint8_t *key; /* defined key */
	    dig_t value ; /* replacement text */
	};

	#define HASHSIZE 10000
	static struct nlist *hashtab[HASHSIZE]; /* pointer table */

/* 	Internal funcion to calculate hash for keys.
	It's based on the DJB algorithm from Daniel J. Bernstein.*/
	unsigned hash(uint8_t *key, int len)
	{
	    unsigned h = 5381;
	    for (int i = 0; i < len; ++i){
			h = ((h << 5) + h) + (*key);
			h++;
	    }
	    return h % HASHSIZE;
	}


	/* lookup: look for s in hashtab */
	struct nlist *lookup(uint8_t *key, int len)
	{
	    struct nlist *np;

/*	    uint8_t digest[MD_LEN];
	    md_map(digest, key, len);	*/    
	    for (np = hashtab[hash(key, len)]; np != NULL; np = np->next)
	        if ( util_cmp_const(key, np->key, len) == CMP_EQ )
	          return np; /* found */
	    printf(":(\n");
	    return NULL; /* not found */
	}

	/* install: put (key, value) in hashtab */
	struct nlist *install(uint8_t *key, dig_t value, int len)
	{
	    struct nlist *np;
	    unsigned hashval;
	    np = (struct nlist *) malloc(sizeof(*np));
	    if (np == NULL)
	      return NULL;
	    np->key = malloc(len * sizeof(uint8_t) );
	    
	    memcpy(np->key, key, len);
	    
/*	    uint8_t digest[MD_LEN];
	    md_map(digest, key, len);*/

	    hashval = hash(key, len);
	    np->next = hashtab[hashval];
	    hashtab[hashval] = np;
	    np->value = value;
	    return np;
	}

#endif
/*============================================================================*/
/* Public definitions                                                         */
/*============================================================================*/

int cp_bgn_gen(bgn_t pub, bgn_t prv) {
	bn_t n, nt, r, r_gt, s_gt;
	g1_t g;
	g2_t s, u, h;
	gt_t st, ut;

	int result = STS_OK;

	bn_null(n);
	bn_null(r);
	
	g2_null(s);
	g2_null(u);
	gt_null(st);
	gt_null(ut);

	TRY {
		bn_new(n);
		bn_new(r);
		
		g2_new(s);
		g2_new(u);
		gt_new(st);
		gt_new(ut);

		g1_get_ord(n);

		bn_rand_mod(prv->x, n);
		bn_rand_mod(prv->y, n);
		bn_rand_mod(prv->z, n);

		g1_mul_gen(pub->gx, prv->x);
		g1_mul_gen(pub->gy, prv->y);
		g1_mul_gen(pub->gz, prv->z);

		g2_mul_gen(pub->hx, prv->x);
		g2_mul_gen(pub->hy, prv->y);
		g2_mul_gen(pub->hz, prv->z);

		bn_mul(r, prv->x, prv->y);
		bn_sub(r, r, prv->z);
		bn_mod(r, r, n);

		g2_mul_gen(s, r);
		g2_copy(u, s);

		g1_get_gen(g);
		g2_get_gen(h);
		gt_get_ord(nt);

		bn_mul(r_gt, prv->x, prv->y);
		bn_sqr(r_gt, r_gt);

		bn_mul(s_gt, prv->x, prv->y);
		bn_mul(s_gt, s_gt, prv->z);
		bn_sub(r_gt, r_gt, s_gt);
		bn_sub(r_gt, r_gt, s_gt);

		bn_sqr(s_gt, prv->z);
		bn_add(r_gt, r_gt, s_gt);
		bn_mod(r_gt, r_gt, nt);
		pc_map(st, g, h);
		gt_exp(st, st, r_gt);
		gt_copy(ut, st);

		#ifdef LUT
			int len = g2_size_bin(u, 1);
			uint8_t buf[len];
			
			int lent = gt_size_bin(ut, 1);
			uint8_t buft[lent];

			for (int i = 0; i < HASHSIZE; ++i) {
				len = g2_size_bin(u, 1);
				g2_write_bin(buf, sizeof(buf), u, 1);

				install(buf, i+1, len);
				
				g2_add(u, u, s);
				g2_norm(u, u);	

				memset(buf, 0, sizeof(buf));
				
				//g_t case
				lent = gt_size_bin(ut, 1);
				gt_write_bin(buft, sizeof(buft), ut, 1);

				install(buft, i+1, lent);
				gt_mul(ut, ut, st);

				memset(buft, 0, sizeof(buft));
			}
		#endif
	}
	CATCH_ANY {
		result = STS_ERR;
	}
	FINALLY {
		bn_free(n);
		bn_free(r);

		g2_free(s);
		g2_free(u);
		gt_free(s);
		gt_free(u);

	}

	return result;
}

int cp_bgn_enc1(g1_t out[2], dig_t in, bgn_t pub) {
	bn_t r, n;
	g1_t t;
	int result = STS_OK;

	bn_null(n);
	bn_null(r);
	g1_null(t);

	TRY {
		bn_new(n);
		bn_new(r);
		g1_new(t);

		g1_get_ord(n);
		bn_rand_mod(r, n);

		/* Compute c0 = (ym + r)G. */
		g1_mul_dig(out[0], pub->gy, in);

		g1_mul_gen(t, r);
		g1_add(out[0], out[0], t);
		g1_norm(out[0], out[0]);

		/* Compute c1 = (zm + xr)G. */
		g1_mul_dig(out[1], pub->gz, in);
		g1_mul(t, pub->gx, r);
		g1_add(out[1], out[1], t);
		g1_norm(out[1], out[1]);
	}
	CATCH_ANY {
		result = STS_ERR;
	}
	FINALLY {
		bn_free(n);
		bn_free(r);
		g1_free(t);
	}

	return result;
}

int cp_bgn_dec1(dig_t *out, g1_t in[2], bgn_t prv) {
	bn_t r, n;
	g1_t s, t, u;
	int i, result = STS_OK;

	bn_null(n);
	bn_null(r);
	g1_null(s);
	g1_null(t);
	g1_null(u);

	TRY {
		bn_new(n);
		bn_new(r);
		g1_new(s);
		g1_new(t);
		g1_new(u);

		g1_get_ord(n);
		/* Compute T = x(ym + r)G - (zm + xr)G = m(xy - z)G. */
		g1_mul(t, in[0], prv->x);
		g1_sub(t, t, in[1]);
		g1_norm(t, t);
		/* Compute U = (xy - z)G and find m. */
		bn_mul(r, prv->x, prv->y);
		bn_sub(r, r, prv->z);
		bn_mod(r, r, n);
		g1_mul_gen(s, r);
		g1_copy(u, s);
		
		if ( g1_is_infty(t) == 1){
			*out = 0;
			break;
		} 		
		for (i = 0; i < INT_MAX; i++) {
			if (g1_cmp(t, u) == CMP_EQ) {
				*out = i + 1;
				break;
			}
			g1_add(u, u, s);
			g1_norm(u, u);			
		}
		
		if (i == INT_MAX) {
			result = STS_ERR;
		}
	} CATCH_ANY {
		result = STS_ERR;
	}
	FINALLY {
		bn_free(n);
		bn_free(r);
		g1_free(s);
		g1_free(t);
		g1_free(u);
	}

	return result;
}

int cp_bgn_enc2(g2_t out[2], dig_t in, bgn_t pub) {
	bn_t r, n;
	g2_t t;
	int result = STS_OK;

	bn_null(n);
	bn_null(r);
	g2_null(t);

	TRY {
		bn_new(n);
		bn_new(r);
		g2_new(t);

		g2_get_ord(n);
		bn_rand_mod(r, n);

		/* Compute c0 = (ym + r)G. */
		g2_mul_dig(out[0], pub->hy, in);
		g2_mul_gen(t, r);
		g2_add(out[0], out[0], t);
		g2_norm(out[0], out[0]);

		/* Compute c1 = (zm + xr)G. */
		g2_mul_dig(out[1], pub->hz, in);
		g2_mul(t, pub->hx, r);
		g2_add(out[1], out[1], t);
		g2_norm(out[1], out[1]);
	}
	CATCH_ANY {
		result = STS_ERR;
	}
	FINALLY {
		bn_free(n);
		bn_free(r);
		g2_free(t);
	}

	return result;
}

int cp_bgn_dec2(dig_t *out, g2_t in[2], bgn_t prv) {
	bn_t r, n;
	g2_t s, t, u;
	int i, result = STS_OK;

	bn_null(n);
	bn_null(r);
	g2_null(s);
	g2_null(t);
	g2_null(u);

	TRY {
		bn_new(n);
		bn_new(r);
		g2_new(s);
		g2_new(t);
		g2_new(u);

		g2_get_ord(n);
		/* Compute T = x(ym + r)G - (zm + xr)G = m(xy - z)G. */
		g2_mul(t, in[0], prv->x);
		g2_sub(t, t, in[1]);
		g2_norm(t, t);
	
		if ( g2_is_infty(t) == 1) {
			*out = 0;
			break;
		} 

		#ifdef LUT
			int len = g2_size_bin(t, 1);
			uint8_t buf[len];
			
			g2_write_bin(buf, sizeof(buf), t, 1);
					
			struct nlist * np;
			np = lookup(buf, len);
			
			if (np != NULL) {
				//printf("Found: %lu \n",np->value );
				*out = np->value;
				break;
			}
		#endif

		/* Compute U = (xy - z)G and find m. */
		bn_mul(r, prv->x, prv->y);
		bn_sub(r, r, prv->z);
		bn_mod(r, r, n);
		g2_mul_gen(s, r);
		g2_copy(u, s);
		

		for (i = 0; i < INT_MAX; i++) {
			if (g2_cmp(t, u) == CMP_EQ) {
				*out = i + 1;
				break;
			}
			g2_add(u, u, s);
			g2_norm(u, u);			
		}

		if (i == INT_MAX) {
			result = STS_ERR;
		}
	} CATCH_ANY {
		result = STS_ERR;
	}
	FINALLY {
		bn_free(n);
		bn_free(r);
		g2_free(s);
		g2_free(t);
		g2_free(u);
	}

	return result;
}


int cp_bgn_sub1(g1_t e[2], g1_t c[2], g1_t d[2]) {
	for (int i = 0; i < 2; i++) {
		g1_sub(e[i], c[i], d[i]);
		g1_norm(e[i], e[i]);
	}
	return STS_OK;
}

int cp_bgn_sub2(g2_t e[2], g2_t c[2], g2_t d[2]) {
	for (int i = 0; i < 2; i++) {
		g2_sub(e[i], c[i], d[i]);
		g2_norm(e[i], e[i]);
	}
	return STS_OK;
}

int cp_bgn_add1(g1_t e[2], g1_t c[2], g1_t d[2]) {
	for (int i = 0; i < 2; i++) {
		g1_add(e[i], c[i], d[i]);
		g1_norm(e[i], e[i]);
	}
	return STS_OK;
}

int cp_bgn_add2(g2_t e[2], g2_t c[2], g2_t d[2]) {
	for (int i = 0; i < 2; i++) {
		g2_add(e[i], c[i], d[i]);
		g2_norm(e[i], e[i]);
	}
	return STS_OK;
}

int cp_bgn_add(gt_t e[4], gt_t c[4], gt_t d[4]) {
	for (int i = 0; i < 4; i++) {
		gt_mul(e[i], c[i], d[i]);
	}
	return STS_OK;
}

int cp_bgn_sub(gt_t e[4], gt_t c[4], gt_t d[4]) {

	for (int i = 0; i < 4; i++) {
		gt_inv(d[i], d[i]);
		gt_mul(e[i], c[i], d[i]);
	}

	return STS_OK;
}

int cp_bgn_mul(gt_t e[4], g1_t c[2], g2_t d[2]) {
	for (int i = 0; i < 2; i++) {
		for (int j = 0; j < 2; j++) {
			pc_map(e[2*i + j], c[i], d[j]);
		}
	}
	return STS_OK;
}

int cp_bgn_dec(dig_t *out, gt_t in[4], bgn_t prv) {
	int i, result = STS_OK;
	g1_t g;
	g2_t h;
	gt_t t[4];
	bn_t n, r, s;

	bn_null(n);
	bn_null(r);
	bn_null(s);
	g1_null(g);
	g2_null(h);

	TRY {
		bn_new(n);
		bn_new(r);
		bn_new(s);
		g1_new(g);
		g2_new(h);
		for (i = 0; i < 4; i++) {
			gt_null(t[i]);
			gt_new(t[i]);
		}

		gt_exp(t[0], in[0], prv->x);
		gt_exp(t[0], t[0], prv->x);

		gt_mul(t[1], in[1], in[2]);
		gt_exp(t[1], t[1], prv->x);
		gt_inv(t[1], t[1]);

		gt_mul(t[3], in[3], t[1]);
		gt_mul(t[3], t[3], t[0]);


		if (gt_is_unity(t[3]) == 1) {
			*out = 0;
			break;
		} 	

		#ifdef LUT
			int len = gt_size_bin(t[3], 1);
			uint8_t buf[len];
			
			gt_write_bin(buf, sizeof(buf), t[3], 1);
					
			struct nlist * np;
			np = lookup(buf, len);
			
			if (np != NULL) {
				*out = np->value;
				break;
			}
		#endif

		gt_get_ord(n);
		g1_get_gen(g);
		g2_get_gen(h);

		bn_mul(r, prv->x, prv->y);
		bn_sqr(r, r);

		bn_mul(s, prv->x, prv->y);
		bn_mul(s, s, prv->z);
		bn_sub(r, r, s);
		bn_sub(r, r, s);

		bn_sqr(s, prv->z);
		bn_add(r, r, s);
		bn_mod(r, r, n);
		pc_map(t[1], g, h);
		gt_exp(t[1], t[1], r);

		gt_copy(t[2], t[1]);

		for (i = 0; i < INT_MAX; i++) {
			if (gt_cmp(t[2], t[3]) == CMP_EQ) {
				*out = i + 1;
				break;
			}
			gt_mul(t[2], t[2], t[1]);
		}

		if (i == INT_MAX) {
			result = STS_ERR;
		}
	} CATCH_ANY {
		result = STS_ERR;
	} FINALLY {
		bn_free(n);
		bn_free(r);
		bn_free(s);
		g1_free(g);
		g2_free(h);		
		for (i = 0; i < 4; i++) {
			gt_free(t[i]);
		}		
	}

	return result;
}