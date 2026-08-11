/*
 * Copyright (c) 2010-2012 Frank Morgner and Dominik Oepen
 *
 * This file is part of OpenPACE.
 *
 * OpenPACE is free software: you can redistribute it and/or modify it under
 * the terms of the GNU General Public License as published by the Free
 * Software Foundation, either version 3 of the License, or (at your option)
 * any later version.
 *
 * OpenPACE is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
 * details.
 *
 * You should have received a copy of the GNU General Public License along with
 * OpenPACE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7
 *
 * If you modify this Program, or any covered work, by linking or combining it
 * with OpenSSL (or a modified version of that library), containing
 * parts covered by the terms of OpenSSL's license, the licensors of
 * this Program grant you additional permission to convey the resulting work.
 * Corresponding Source for a non-source form of such a combination shall include
 * the source code for the parts of OpenSSL used as well as that of the
 * covered work.
 *
 * If you modify this Program, or any covered work, by linking or combining it
 * with OpenSC (or a modified version of that library), containing
 * parts covered by the terms of OpenSC's license, the licensors of
 * this Program grant you additional permission to convey the resulting work. 
 * Corresponding Source for a non-source form of such a combination shall include
 * the source code for the parts of OpenSC used as well as that of the
 * covered work.
 */

/**
 * @file pace_mappings.c
 * @brief Functions for domain parameter mappings
 *
 * @author Frank Morgner <frankmorgner@gmail.com>
 * @author Dominik Oepen <oepen@informatik.hu-berlin.de>
 */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "eac_dh.h"
#include "eac_ecdh.h"
#include "eac_err.h"
#include "eac_util.h"
#include "misc.h"
#include "pace_mappings.h"
#include "ssl_compat.h"
#include <openssl/bn.h>
#include <openssl/crypto.h>
#include <openssl/ec.h>
#include <openssl/ecdh.h>

/* ICAO 9303-11, 4.4.3.3.2, Figure 2.  Integrated Mapping does not map
 * E_t(s) directly.  It expands s and t with the iterated CBC construction
 * and only then reduces the result modulo the field prime. */
static BUF_MEM *
im_pseudo_random(const PACE_CTX *ctx, const BUF_MEM *s, const BUF_MEM *t,
        const BIGNUM *p, BN_CTX *bn_ctx)
{
    static const unsigned char c0_128[] = {
        0xa6, 0x68, 0x89, 0x2a, 0x7c, 0x41, 0xe3, 0xca,
        0x73, 0x9f, 0x40, 0xb0, 0x57, 0xd8, 0x59, 0x04
    };
    static const unsigned char c1_128[] = {
        0xa4, 0xe1, 0x36, 0xac, 0x72, 0x5f, 0x73, 0x8b,
        0x01, 0xc1, 0xf6, 0x02, 0x17, 0xc1, 0x88, 0xad
    };
    static const unsigned char c0_256[] = {
        0xd4, 0x63, 0xd6, 0x52, 0x34, 0x12, 0x4e, 0xf7,
        0x89, 0x70, 0x54, 0x98, 0x6d, 0xca, 0x0a, 0x17,
        0x4e, 0x28, 0xdf, 0x75, 0x8c, 0xba, 0xa0, 0x3f,
        0x24, 0x06, 0x16, 0x41, 0x4d, 0x5a, 0x16, 0x76
    };
    static const unsigned char c1_256[] = {
        0x54, 0xbd, 0x72, 0x55, 0xf0, 0xaa, 0xf8, 0x31,
        0xbe, 0xc3, 0x42, 0x3f, 0xcf, 0x39, 0xd6, 0x9b,
        0x6c, 0xbf, 0x06, 0x66, 0x77, 0xd0, 0xfa, 0xae,
        0x5a, 0xad, 0xd9, 0x9d, 0xf8, 0xe5, 0x35, 0x17
    };
    BUF_MEM *c0 = NULL, *c1 = NULL, *key = NULL, *k = NULL;
    BUF_MEM *next = NULL, *x = NULL, *expanded = NULL, *result = NULL;
    BIGNUM *expanded_bn = NULL, *reduced_bn = NULL;
    const unsigned char *c0_data, *c1_data;
    size_t constant_length, key_length, iterations, i;
    int required_bits;

    check(ctx && ctx->ka_ctx && ctx->ka_ctx->cipher && s && t && p,
            "Invalid arguments");

    key_length = EVP_CIPHER_key_length(ctx->ka_ctx->cipher);
    check(t->length == key_length && s->length > 0, "Invalid IM nonce length");
    if (key_length <= 16) {
        c0_data = c0_128;
        c1_data = c1_128;
        constant_length = sizeof(c0_128);
    } else {
        c0_data = c0_256;
        c1_data = c1_256;
        constant_length = sizeof(c0_256);
    }
    check(s->length == constant_length, "Invalid IM chip nonce length");

    required_bits = BN_num_bits(p) + 64;
    iterations = ((size_t) required_bits + s->length * 8 - 1)
        / (s->length * 8);
    c0 = BUF_MEM_create_init(c0_data, constant_length);
    c1 = BUF_MEM_create_init(c1_data, constant_length);
    expanded = BUF_MEM_new();
    check(c0 && c1 && expanded
            && BUF_MEM_grow(expanded, iterations * s->length),
            "Failed to initialize IM pseudo-random mapping");

    /* k0 = E_t(s). */
    k = cipher_no_pad(ctx->ka_ctx, NULL, t, s, 1);
    check(k && k->length == s->length, "Failed to initialize IM mapping");

    for (i = 0; i < iterations; i++) {
        /* AES-192 uses the first 24 octets of k_i as the next key. */
        key = BUF_MEM_create_init(k->data, key_length);
        check(key, "Failed to create IM iteration key");
        x = cipher_no_pad(ctx->ka_ctx, NULL, key, c1, 1);
        next = cipher_no_pad(ctx->ka_ctx, NULL, key, c0, 1);
        check(x && next && x->length == s->length
                && next->length == s->length,
                "Failed to expand IM pseudo-random mapping");
        memcpy(expanded->data + i * s->length, x->data, s->length);
        BUF_MEM_clear_free(key);
        key = NULL;
        BUF_MEM_clear_free(x);
        x = NULL;
        BUF_MEM_clear_free(k);
        k = next;
        next = NULL;
    }

    expanded_bn = BN_bin2bn((unsigned char *) expanded->data,
            expanded->length, NULL);
    reduced_bn = BN_new();
    check(expanded_bn && reduced_bn
            && BN_nnmod(reduced_bn, expanded_bn, p, bn_ctx),
            "Failed to reduce IM pseudo-random mapping");
    result = BN_bn2buf(reduced_bn);

err:
    BUF_MEM_clear_free(c0);
    BUF_MEM_clear_free(c1);
    BUF_MEM_clear_free(key);
    BUF_MEM_clear_free(k);
    BUF_MEM_clear_free(next);
    BUF_MEM_clear_free(x);
    BUF_MEM_clear_free(expanded);
    BN_clear_free(expanded_bn);
    BN_clear_free(reduced_bn);
    return result;
}

BUF_MEM *
dh_gm_generate_key(const PACE_CTX * ctx, BN_CTX *bn_ctx)
{
    check_return(ctx, "Invalid arguments");

    return dh_generate_key(ctx->static_key, bn_ctx);
}

int
dh_gm_compute_key(PACE_CTX * ctx, const BUF_MEM * s, const BUF_MEM * in,
        BN_CTX *bn_ctx)
{
    int ret = 0;
    BUF_MEM * mem_h = NULL;
    BIGNUM * bn_s = NULL, *bn_h = NULL, *bn_g = NULL, *new_g = NULL;
    DH *static_key = NULL, *ephemeral_key = NULL;
    const BIGNUM *p, *q, *g;

    check(ctx && ctx->static_key && s && ctx->ka_ctx, "Invalid arguments");

    BN_CTX_start(bn_ctx);

    static_key = EVP_PKEY_get1_DH(ctx->static_key);
    if (!static_key)
        goto err;

    /* Convert nonce to BIGNUM */
    bn_s = BN_bin2bn((unsigned char *) s->data, s->length, bn_s);
    if (!bn_s)
        goto err;

    /* complete the DH and convert the result to a BIGNUM */
    mem_h = dh_compute_key(ctx->static_key, in, bn_ctx);
    if (!mem_h)
        goto err;
    bn_h = BN_bin2bn((unsigned char *) mem_h->data, mem_h->length, bn_h);
    if (!bn_h)
        goto err;

    /* Initialize ephemeral parameters with parameters from the static key */
    ephemeral_key = DHparams_dup(static_key);
    if (!ephemeral_key)
        goto err;

    DH_get0_pqg(static_key, &p, &q, &g);

    /* map to new generator */
    bn_g = BN_CTX_get(bn_ctx);
    new_g = BN_new();
    if (!bn_g || !new_g ||
        /* bn_g = g^s mod p */
        !BN_mod_exp(bn_g, g, bn_s, p, bn_ctx) ||
        /* ephemeral_key->g = bn_g * h mod p = g^s * h mod p */
        !BN_mod_mul(new_g, bn_g, bn_h, p, bn_ctx))
        goto err;

    if (!DH_set0_pqg(ephemeral_key, BN_dup(p), BN_dup(q), new_g))
        goto err;
    new_g = NULL;

    /* Copy ephemeral key to context structure */
    if (!EVP_PKEY_set1_DH(ctx->ka_ctx->key, ephemeral_key))
        goto err;

    ret = 1;

err:
    if (mem_h) {
        OPENSSL_cleanse(mem_h->data, mem_h->max);
        BUF_MEM_free(mem_h);
    }
    if (bn_h)
        BN_clear_free(bn_h);
    if (bn_s)
        BN_clear_free(bn_s);
    /* Decrement reference count, keys are still available via PACE_CTX */
    if (static_key)
        DH_free(static_key);
    if (ephemeral_key)
        DH_free(ephemeral_key);
    BN_CTX_end(bn_ctx);
    if (new_g)
        BN_clear_free(new_g);

    return ret;
}

BUF_MEM *
dh_im_generate_key(const PACE_CTX * ctx, BN_CTX *bn_ctx)
{
    check_return((ctx && ctx->ka_ctx), "Invalid arguments");

    return randb(EVP_CIPHER_key_length(ctx->ka_ctx->cipher));
}

int
dh_im_compute_key(PACE_CTX * ctx, const BUF_MEM * s, const BUF_MEM * in,
        BN_CTX *bn_ctx)
{
    int ret = 0;
    BUF_MEM * x_mem = NULL;
    BIGNUM * x_bn = NULL, *a = NULL, *p_1 = NULL, *q = NULL, *g_new = NULL;
    const BIGNUM *p, *g;
    DH *static_key = NULL, *ephemeral_key = NULL;

    check((ctx && in && ctx->ka_ctx), "Invalid arguments");
    if (in->length < (size_t) EVP_CIPHER_key_length(ctx->ka_ctx->cipher)
            || !ctx->static_key)
        goto err;

    BN_CTX_start(bn_ctx);

    static_key = EVP_PKEY_get1_DH(ctx->static_key);
    if (!static_key)
        goto err;

    /* Initialize ephemeral parameters with parameters from the static key */
    ephemeral_key = DHparams_dup_with_q(static_key);
    if (!ephemeral_key)
        goto err;
    DH_get0_pqg(ephemeral_key, &p, NULL, &g);

    a = BN_CTX_get(bn_ctx);
    q = DH_get_q(static_key, bn_ctx);
    p_1 = BN_dup(p);
    g_new = BN_dup(g);
    /* Perform the actual mapping. */
    x_mem = im_pseudo_random(ctx, s, in, p, bn_ctx);
    if (!x_mem)
        goto err;
    x_bn = BN_bin2bn((unsigned char *) x_mem->data, x_mem->length, x_bn);
    if (!x_bn || !a || !q || !p_1 || !g_new ||
            /* p_1 = p-1 */
            !BN_sub_word(p_1, 1) ||
            /* a = p-1 / q */
            !BN_div(a, NULL, p_1, q, bn_ctx) ||
            /* g~ = x^a mod p */
            !BN_mod_exp(g_new, x_bn, a, p, bn_ctx))
        goto err;

    /* check if g~ != 1 */
    check((!BN_is_one(g_new)), "Bad DH generator");

    DH_set0_pqg(ephemeral_key, BN_dup(p), q, g_new);
    g_new = NULL;
    q = NULL;

    /* Copy ephemeral key to context structure */
    if (!EVP_PKEY_set1_DH(ctx->ka_ctx->key, ephemeral_key))
        goto err;

    ret = 1;

err:
    if (q)
        BN_clear_free(q);
    if (g_new)
        BN_clear_free(g_new);
    if (p_1)
        BN_clear_free(p_1);
    if (x_bn)
        BN_clear_free(x_bn);
    if (x_mem)
        BUF_MEM_free(x_mem);
    /* Decrement reference count, keys are still available via PACE_CTX */
    if (static_key)
        DH_free(static_key);
    if (ephemeral_key)
        DH_free(ephemeral_key);
    BN_CTX_end(bn_ctx);

    return ret;
}

BUF_MEM *
ecdh_gm_generate_key(const PACE_CTX * ctx, BN_CTX *bn_ctx)
{
    check_return(ctx, "Invalid arguments");

    return ecdh_generate_key(ctx->static_key, bn_ctx);
}

int
ecdh_gm_compute_key(PACE_CTX * ctx, const BUF_MEM * s, const BUF_MEM * in,
        BN_CTX *bn_ctx)
{
    int ret = 0;
    BUF_MEM * mem_h = NULL;
    BIGNUM * bn_s = NULL, *order = NULL, *cofactor = NULL;
    EC_POINT * ecp_h = NULL, *ecp_g = NULL;
    EC_GROUP *group = NULL;
    EC_KEY *static_key = NULL, *ephemeral_key = NULL;
#ifdef HAVE_EC_KEY_METHOD
    const EC_KEY_METHOD *default_method;
#else
    const ECDH_METHOD *default_method;
#endif

    BN_CTX_start(bn_ctx);

    check((ctx && ctx->static_key && s && ctx->ka_ctx), "Invalid arguments");

    static_key = EVP_PKEY_get1_EC_KEY(ctx->static_key);
    check(static_key, "could not get key object");

    /* Extract group parameters */
    group = EC_GROUP_dup(EC_KEY_get0_group(static_key));
    order = BN_CTX_get(bn_ctx);
    cofactor = BN_CTX_get(bn_ctx);
    check(group && cofactor, "internal error");
    if (!EC_GROUP_get_order(group, order, bn_ctx)
            || !EC_GROUP_get_cofactor(group, cofactor, bn_ctx))
        goto err;

    /* Convert nonce to BIGNUM */
    bn_s = BN_bin2bn((unsigned char *) s->data, s->length, bn_s);
    if (!bn_s)
        goto err;

#ifdef HAVE_EC_KEY_METHOD
    default_method = EC_KEY_get_method(static_key);
    if (!EC_KEY_set_method(static_key, EC_KEY_OpenSSL_Point()))
        goto err;
    /* complete the ECDH and get the resulting point h */
    mem_h = ecdh_compute_key(ctx->static_key, in, bn_ctx);
    EC_KEY_set_method(static_key, default_method);
#else
    default_method = ECDH_get_default_method();
    ECDH_set_default_method(ECDH_OpenSSL_Point());
    /* complete the ECDH and get the resulting point h */
    mem_h = ecdh_compute_key(ctx->static_key, in, bn_ctx);
    ECDH_set_default_method(default_method);
#endif
    ecp_h = EC_POINT_new(group);
    if (!mem_h || !ecp_h || !EC_POINT_oct2point(group, ecp_h,
            (unsigned char *) mem_h->data, mem_h->length, bn_ctx))
        goto err;

    /* map to new generator */
    ecp_g = EC_POINT_new(group);
    /* g' = g*s + h*1 */
    if (!EC_POINT_mul(group, ecp_g, bn_s, ecp_h, BN_value_one(), bn_ctx))
        goto err;

    /* Initialize ephemeral parameters with parameters from the static key */
    ephemeral_key = EC_KEY_dup(static_key);
    if (!ephemeral_key)
        goto err;
    EVP_PKEY_set1_EC_KEY(ctx->ka_ctx->key, ephemeral_key);

    /* configure the new EC_KEY */
    if (!EC_GROUP_set_generator(group, ecp_g, order, cofactor)
            || !EC_GROUP_check(group, bn_ctx)
            || !EC_KEY_set_group(ephemeral_key, group))
        goto err;

    ret = 1;

err:
    if (ecp_g)
        EC_POINT_clear_free(ecp_g);
    if (ecp_h)
        EC_POINT_clear_free(ecp_h);
    if (mem_h)
        BUF_MEM_free(mem_h);
    if (bn_s)
        BN_clear_free(bn_s);
    BN_CTX_end(bn_ctx);
    /* Decrement reference count, keys are still available via PACE_CTX */
    if (static_key)
        EC_KEY_free(static_key);
    if (ephemeral_key)
        EC_KEY_free(ephemeral_key);
    if (group)
        EC_GROUP_clear_free(group);

    return ret;
}

BUF_MEM *
ecdh_im_generate_key(const PACE_CTX * ctx, BN_CTX *bn_ctx)
{
    check_return((ctx && ctx->ka_ctx), "Invalid arguments");

    return randb(EVP_CIPHER_key_length(ctx->ka_ctx->cipher));
}

int
ecdh_im_compute_key(PACE_CTX * ctx, const BUF_MEM * s, const BUF_MEM * in,
        BN_CTX *bn_ctx)
{
    int ret = 0;
    BUF_MEM * x_mem = NULL;
    BIGNUM * a = NULL, *b = NULL, *p = NULL;
    BIGNUM * x = NULL, *y = NULL, *v = NULL, *u = NULL;
    BIGNUM * tmp = NULL, *tmp2 = NULL, *bn_inv = NULL;
    BIGNUM * alpha = NULL, *x2 = NULL, *x3 = NULL, *h2 = NULL;
    BIGNUM * exponent = NULL, *order = NULL, *cofactor = NULL;
    BIGNUM * two = NULL, *three = NULL, *four = NULL, *six = NULL;
    BIGNUM * twentyseven = NULL;
    EC_KEY *static_key = NULL, *ephemeral_key = NULL;
    EC_POINT *g = NULL;
    EC_GROUP *group = NULL;

    BN_CTX_start(bn_ctx);

    check((ctx && ctx->static_key && s && ctx->ka_ctx), "Invalid arguments"); 

    static_key = EVP_PKEY_get1_EC_KEY(ctx->static_key);
    if (!static_key)
        goto err;

    /* Setup all the variables*/
    a = BN_CTX_get(bn_ctx);
    b = BN_CTX_get(bn_ctx);
    p = BN_CTX_get(bn_ctx);
    x = BN_CTX_get(bn_ctx);
    y = BN_CTX_get(bn_ctx);
    v = BN_CTX_get(bn_ctx);
    two = BN_CTX_get(bn_ctx);
    three = BN_CTX_get(bn_ctx);
    four = BN_CTX_get(bn_ctx);
    six = BN_CTX_get(bn_ctx);
    twentyseven = BN_CTX_get(bn_ctx);
    tmp = BN_CTX_get(bn_ctx);
    tmp2 = BN_CTX_get(bn_ctx);
    bn_inv = BN_CTX_get(bn_ctx);
    alpha = BN_CTX_get(bn_ctx);
    x2 = BN_CTX_get(bn_ctx);
    x3 = BN_CTX_get(bn_ctx);
    h2 = BN_CTX_get(bn_ctx);
    exponent = BN_CTX_get(bn_ctx);
    order = BN_CTX_get(bn_ctx);
    cofactor = BN_CTX_get(bn_ctx);
    if (!cofactor)
        goto err;

    /* Fetch the curve parameters */
    if (!EC_GROUP_get_curve_GFp(EC_KEY_get0_group(static_key), p, a, b, bn_ctx))
        goto err;

    /* Expand and reduce both nonces as required by Integrated Mapping. */
    x_mem = im_pseudo_random(ctx, s, in, p, bn_ctx);
    if (!x_mem)
        goto err;

    /* Assign constants */
    if (    !BN_set_word(two,2)||
            !BN_set_word(three,3)||
            !BN_set_word(four,4)||
            !BN_set_word(six,6)||
            !BN_set_word(twentyseven,27)
            ) goto err;

    /* Convert encrypted nonce to BIGNUM */
    u = BN_bin2bn((unsigned char *) x_mem->data, x_mem->length, u);
    if (!u)
        goto err;

    /* ICAO Doc 9303-11, Appendix B.2: point encoding for affine
     * coordinates.  The former Icart-only implementation required
     * p = 2 mod 3 and rejected five standardized PACE curves. */
    check((BN_cmp(p, three) == 1) && !BN_is_zero(u), "Unsuited curve");
    check(BN_mod_word(p, 4) == 3, "Point encoding requires p = 3 mod 4");
    if (
            /* 1. alpha = -t^2 mod p */
            !BN_mod_sqr(alpha, u, p, bn_ctx) ||
            !BN_mod_sub(alpha, BN_value_one(), alpha, p, bn_ctx) ||
            !BN_mod_sub(alpha, alpha, BN_value_one(), p, bn_ctx) ||
            /* 2. X2 = -b/a * (1 + 1/(alpha + alpha^2)) */
            !BN_mod_sqr(tmp, alpha, p, bn_ctx) ||
            !BN_mod_add(tmp, alpha, tmp, p, bn_ctx) ||
            !BN_mod_inverse(bn_inv, tmp, p, bn_ctx) ||
            !BN_mod_add(tmp, BN_value_one(), bn_inv, p, bn_ctx) ||
            !BN_mod_inverse(bn_inv, a, p, bn_ctx) ||
            !BN_mod_mul(x2, b, bn_inv, p, bn_ctx) ||
            !BN_mod_mul(x2, x2, tmp, p, bn_ctx) ||
            !BN_mod_sub(x2, BN_value_one(), x2, p, bn_ctx) ||
            !BN_mod_sub(x2, x2, BN_value_one(), p, bn_ctx) ||
            /* 3. X3 = alpha * X2 */
            !BN_mod_mul(x3, alpha, x2, p, bn_ctx) ||
            /* 4. h2 = X2^3 + a*X2 + b */
            !BN_mod_sqr(tmp, x2, p, bn_ctx) ||
            !BN_mod_mul(h2, tmp, x2, p, bn_ctx) ||
            !BN_mod_mul(tmp, a, x2, p, bn_ctx) ||
            !BN_mod_add(h2, h2, tmp, p, bn_ctx) ||
            !BN_mod_add(h2, h2, b, p, bn_ctx) ||
            /* 6. U = t^3 * h2 (reuse v for U) */
            !BN_mod_sqr(tmp, u, p, bn_ctx) ||
            !BN_mod_mul(tmp, tmp, u, p, bn_ctx) ||
            !BN_mod_mul(v, tmp, h2, p, bn_ctx) ||
            /* 7. A = h2^(p-1-(p+1)/4) */
            !BN_copy(exponent, p) || !BN_sub_word(exponent, 1) ||
            !BN_copy(tmp, p) || !BN_add_word(tmp, 1) ||
            !BN_rshift(tmp, tmp, 2) ||
            !BN_sub(exponent, exponent, tmp) ||
            !BN_mod_exp(y, h2, exponent, p, bn_ctx) ||
            /* Test A^2*h2 == 1. */
            !BN_mod_sqr(tmp, y, p, bn_ctx) ||
            !BN_mod_mul(tmp, tmp, h2, p, bn_ctx))
        goto err;
    if (BN_is_one(tmp)) {
        if (!BN_copy(x, x2) || !BN_mod_mul(y, y, h2, p, bn_ctx))
            goto err;
    } else {
        if (!BN_copy(x, x3) || !BN_mod_mul(y, y, v, p, bn_ctx))
            goto err;
    }

    /* Initialize ephemeral parameters with parameters from the static key */
    ephemeral_key = EC_KEY_dup(static_key);
    if (!ephemeral_key)
        goto err;
    EVP_PKEY_set1_EC_KEY(ctx->ka_ctx->key, ephemeral_key);

    /* configure the new EC_KEY */
    group = EC_GROUP_dup(EC_KEY_get0_group(ephemeral_key));
    g = EC_POINT_new(group);
    if (!group || !g ||
            !EC_GROUP_get_order(group, order, bn_ctx) ||
            !EC_GROUP_get_cofactor(group, cofactor, bn_ctx))
        goto err;
    if (!EC_POINT_set_affine_coordinates(group, g, x, y, bn_ctx) ||
            (!BN_is_one(cofactor) &&
             !EC_POINT_mul(group, g, NULL, g, cofactor, bn_ctx)) ||
            !EC_GROUP_set_generator(group, g, order, cofactor) ||
            !EC_GROUP_check(group, bn_ctx) ||
            !EC_KEY_set_group(ephemeral_key, group))
        goto err;

    ret = 1;

err:
    if (x_mem)
        BUF_MEM_free(x_mem);
    if (u)
        BN_free(u);
    BN_CTX_end(bn_ctx);
    if (g)
        EC_POINT_clear_free(g);
    if (group)
        EC_GROUP_clear_free(group);
    /* Decrement reference count, keys are still available via PACE_CTX */
    if (static_key)
        EC_KEY_free(static_key);
    if (ephemeral_key)
        EC_KEY_free(ephemeral_key);

    return ret;
}
