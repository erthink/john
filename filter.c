// gcc -std=c99 -Wall -pedantic ngpg2john.c -lgcrypt  # compile
//
// $ ../run/john --stdout --mask='password' | ./filter target.key  # use
//
// Use "gpg --with-keygrip -K" to identify the .key file to attack.
// The "Keygrip" associated with "ssb" (out of "ssb" / "sec" value) needs to be
// used.
//
// NOTE: A*.key file pair (main key and subkey) cannot be used by gpg2 if the
// corresponding public key is missing from the pubring.kbx file.
//
// Thanks to K_F (from #gnupg channel on freenode) for all the help.
//
// Hacked together by Dhiru Kholia (dhiru at openwall.com)

/* sexp-parse.h - S-expression helper functions
 * Copyright (C) 2002, 2003, 2007 Free Software Foundation, Inc.
 *
 * This file is free software; you can redistribute it and/or modify
 * it under the terms of either
 *
 *   - the GNU Lesser General Public License as published by the Free
 *     Software Foundation; either version 3 of the License, or (at
 *     your option) any later version.
 *
 * or
 *
 *   - the GNU General Public License as published by the Free
 *     Software Foundation; either version 2 of the License, or (at
 *     your option) any later version.
 *
 * or both in parallel, as here.
 *
 * This file is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, see <http://www.gnu.org/licenses/>.
 */

#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

/* Return the length of the next S-Exp part and update the pointer to
   the first data byte.  0 is returned on error */
static inline size_t snext(unsigned char const **buf) {
  const unsigned char *s;
  int n;

  s = *buf;
  for (n = 0; *s && *s != ':' && (*s >= '0' && *s <= '9'); s++)
    n = n * 10 + (*s - '0');
  if (!n || *s != ':')
    return 0; /* we don't allow empty lengths */
  *buf = s + 1;
  return n;
}

/* Skip over the S-Expression BUF points to and update BUF to point to
   the character right behind.  DEPTH gives the initial number of open
   lists and may be passed as a positive number to skip over the
   remainder of an S-Expression if the current position is somewhere
   in an S-Expression.  The function may return an error code if it
   encounters an impossible condition.  */
static inline int sskip(unsigned char const **buf, int *depth) {
  const unsigned char *s = *buf;
  size_t n;
  int d = *depth;

  while (d > 0) {
    if (*s == '(') {
      d++;
      s++;
    } else if (*s == ')') {
      d--;
      s++;
    } else {
      if (!d)
        return 45; // GPG_ERR_INV_SEXP
      n = snext(&s);
      if (!n)
        return 45; // GPG_ERR_INV_SEXP;
      s += n;
    }
  }
  *buf = s;
  *depth = d;
  return 0;
}

/* Check whether the the string at the address BUF points to matches
   the token.  Return true on match and update BUF to point behind the
   token.  Return false and do not update the buffer if it does not
   match. */
static inline int smatch(unsigned char const **buf, size_t buflen,
                         const char *token) {
  size_t toklen = strlen(token);

  if (buflen != toklen || memcmp(*buf, token, toklen))
    return 0;
  *buf += toklen;
  return 1;
}

/* Format VALUE for use as the length indicatior of an S-expression.
   The caller needs to provide a buffer HELP_BUFFER wth a length of
   HELP_BUFLEN.  The return value is a pointer into HELP_BUFFER with
   the formatted length string.  The colon and a trailing nul are
   appended.  HELP_BUFLEN must be at least 3 - a more useful value is
   15.  If LENGTH is not NULL, the LENGTH of the resulting string
   (excluding the terminating nul) is stored at that address. */
static inline char *smklen(char *help_buffer, size_t help_buflen, size_t value,
                           size_t *length) {
  char *p = help_buffer + help_buflen;

  if (help_buflen >= 3) {
    *--p = 0;
    *--p = ':';
    do {
      *--p = '0' + (value % 10);
      value /= 10;
    } while (value && p > help_buffer);
  }

  if (length)
    *length = (help_buffer + help_buflen) - p;
  return p;
}

/* protect.c - Un/Protect a secret key
 * Copyright (C) 1998-2003, 2007, 2009, 2011 Free Software Foundation, Inc.
 * Copyright (C) 1998-2003, 2007, 2009, 2011, 2013-2015 Werner Koch
 *
 * This file is part of GnuPG.
 *
 * GnuPG is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * GnuPG is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, see <http://www.gnu.org/licenses/>.
 */

// #include "sexp-parse.h"
#include <gcrypt.h>

#define DIM(v) (sizeof(v) / sizeof((v)[0]))

#if GCRYPT_VERSION_NUMBER < 0x010700
#define OCB_MODE_SUPPORTED 0
#else
#define OCB_MODE_SUPPORTED 1
#endif

/* To use the openpgp-s2k3-ocb-aes scheme by default set the value of
 * this macro to 1.  Note that the caller of agent_protect may
 * override this default.  */
#define PROT_DEFAULT_TO_OCB 0

/* The protection mode for encryption.  The supported modes for
   decryption are listed in agent_unprotect().  */
#define PROT_CIPHER GCRY_CIPHER_AES128
#define PROT_CIPHER_STRING "aes"
#define PROT_CIPHER_KEYLEN (128 / 8)

/* Decode an rfc4880 encoded S2K count.  */
#define S2K_DECODE_COUNT(_val) ((16ul + ((_val)&15)) << (((_val) >> 4) + 6))

/* fake defines */
#define GPG_ERR_UNSUPPORTED_ALGORITHM -1
#define GPG_ERR_CORRUPTED_PROTECTION -2
#define GPG_ERR_UNSUPPORTED_PROTECTION -3
#define GPG_ERR_UNKNOWN_SEXP -4

/* A table containing the information needed to create a protected
   private key.  */
static struct {
  const char *algo;
  const char *parmlist;
  int prot_from, prot_to;
  int ecc_hack;
} protect_info[] = {{"rsa", "nedpqu", 2, 5},
                    {"dsa", "pqgyx", 4, 4},
                    {"elg", "pgyx", 3, 3},
                    {"ecdsa", "pabgnqd", 6, 6, 1},
                    {"ecdh", "pabgnqd", 6, 6, 1},
                    {"ecc", "pabgnqd", 6, 6, 1},
                    {NULL}};

/* Transform a passphrase into a suitable key of length KEYLEN and
   store this key in the caller provided buffer KEY.  The caller must
   provide an HASHALGO, a valid S2KMODE (see rfc-2440) and depending on
   that mode an S2KSALT of 8 random bytes and an S2KCOUNT.

   Returns an error code on failure.  */
static int hash_passphrase(const char *passphrase, int hashalgo, int s2kmode,
                           const unsigned char *s2ksalt, unsigned long s2kcount,
                           unsigned char *key, size_t keylen) {
  /* The key derive function does not support a zero length string for
     the passphrase in the S2K modes.  Return a better suited error
     code than GPG_ERR_INV_DATA.  */
  if (!passphrase || !*passphrase)
    return gpg_error(GPG_ERR_NO_PASSPHRASE);
  return gcry_kdf_derive(passphrase, strlen(passphrase),
                         s2kmode == 3
                             ? GCRY_KDF_ITERSALTED_S2K
                             : s2kmode == 1 ? GCRY_KDF_SALTED_S2K
                                            : s2kmode == 0 ? GCRY_KDF_SIMPLE_S2K
                                                           : GCRY_KDF_NONE,
                         hashalgo, s2ksalt, 8, s2kcount, keylen, key);
}

/* Do the actual decryption and check the return list for consistency.  */
int do_decryption(const unsigned char *aad_begin, size_t aad_len,
                  const unsigned char *aadhole_begin, size_t aadhole_len,
                  const unsigned char *protected, size_t protectedlen,
                  const char *passphrase, const unsigned char *s2ksalt,
                  unsigned long s2kcount, const unsigned char *iv, size_t ivlen,
                  int prot_cipher, int prot_cipher_keylen, int is_ocb,
                  unsigned char **result) {
  int rc = 0;
  int blklen;
  gcry_cipher_hd_t hd;
  unsigned char *outbuf;
  size_t reallen;

  if (is_ocb && !OCB_MODE_SUPPORTED)
    return (GPG_ERR_UNSUPPORTED_PROTECTION);

  blklen = gcry_cipher_get_algo_blklen(prot_cipher);
  if (is_ocb) {
    /* OCB does not require a multiple of the block length but we
     * check that it is long enough for the 128 bit tag and that we
     * have the 96 bit nonce.  */
    if (protectedlen < (4 + 16) || ivlen != 12)
      return (GPG_ERR_CORRUPTED_PROTECTION);
  } else {
    if (protectedlen < 4 || (protectedlen % blklen))
      return (GPG_ERR_CORRUPTED_PROTECTION);
  }

  rc = gcry_cipher_open(&hd, prot_cipher,
#if OCB_MODE_SUPPORTED
                        is_ocb ? GCRY_CIPHER_MODE_OCB :
#endif
                               GCRY_CIPHER_MODE_CBC,
                        GCRY_CIPHER_SECURE);
  if (rc)
    return rc;

  outbuf = gcry_malloc_secure(protectedlen);
  if (!outbuf)
    rc = -99; // out_of_core ();

  /* Hash the passphrase and set the key.  */
  if (!rc) {
    unsigned char *key;

    key = gcry_malloc_secure(prot_cipher_keylen);
    if (!key)
      rc = -99; // out_of_core ();
    else {
      rc = hash_passphrase(passphrase, GCRY_MD_SHA1, 3, s2ksalt, s2kcount, key,
                           prot_cipher_keylen); // 3 -> s2k-mode
      // gpg --s2k-count is only meaningful if --s2k-mode is 3, see man gpg,
      // SPEC_ITERATED_SALTED = 3
      if (!rc)
        rc = gcry_cipher_setkey(hd, key, prot_cipher_keylen);
    }
  }

  /* Set the IV/nonce.  */
  if (!rc) {
    rc = gcry_cipher_setiv(hd, iv, ivlen);
  }

  /* Decrypt.  */
  if (!rc) {
#if OCB_MODE_SUPPORTED
    if (is_ocb) {
      rc = gcry_cipher_authenticate(hd, aad_begin, aadhole_begin - aad_begin);
      if (!rc)
        rc = gcry_cipher_authenticate(
            hd, aadhole_begin + aadhole_len,
            aad_len - (aadhole_begin + aadhole_len - aad_begin));

      if (!rc) {
        gcry_cipher_final(hd);
        rc = gcry_cipher_decrypt(hd, outbuf, protectedlen - 16, protected,
                                 protectedlen - 16);
      }
      if (!rc)
        rc = gcry_cipher_checktag(hd, protected + protectedlen - 16, 16);
    } else
#endif /*OCB_MODE_SUPPORTED*/
    {
      rc = gcry_cipher_decrypt(hd, outbuf, protectedlen, protected,
                               protectedlen);
    }
  }

  /* Release cipher handle and check for errors.  */
  gcry_cipher_close(hd);
  if (rc) {
    // xfree (outbuf);
    return rc;
  }

  /* Do a quick check on the data structure. */
  if (*outbuf != '(' && outbuf[1] != '(') {
    /* Note that in OCB mode this is actually invalid _encrypted_
     * data and not a bad passphrase.  */
    // xfree (outbuf);
    return (GPG_ERR_BAD_PASSPHRASE); // GPG_ERR_BAD_PASSPHRASE is 11
  }

  /* Check that we have a consistent S-Exp. */
  reallen = gcry_sexp_canon_len(outbuf, protectedlen, NULL, NULL);
  if (!reallen || (reallen + blklen < protectedlen)) {
    // xfree (outbuf);
    return (GPG_ERR_BAD_PASSPHRASE);
  }
  *result = outbuf;
  return 0;
}

/* Calculate the MIC for a private key or shared secret S-expression.
   SHA1HASH should point to a 20 byte buffer.  This function is
   suitable for all algorithms. */
int calculate_mic(const unsigned char *plainkey, unsigned char *sha1hash) {
  const unsigned char *hash_begin, *hash_end;
  const unsigned char *s;
  size_t n;
  int is_shared_secret;

  s = plainkey;
  if (*s != '(')
    return (GPG_ERR_INV_SEXP);
  s++;
  n = snext(&s);
  if (!n)
    return (GPG_ERR_INV_SEXP);
  if (smatch(&s, n, "private-key"))
    is_shared_secret = 0;
  else if (smatch(&s, n, "shared-secret"))
    is_shared_secret = 1;
  else
    return (GPG_ERR_UNKNOWN_SEXP);
  if (*s != '(')
    return (GPG_ERR_UNKNOWN_SEXP);
  hash_begin = s;
  if (!is_shared_secret) {
    s++;
    n = snext(&s);
    if (!n)
      return (GPG_ERR_INV_SEXP);
    s += n; /* Skip the algorithm name.  */
  }

  while (*s == '(') {
    s++;
    n = snext(&s);
    if (!n)
      return (GPG_ERR_INV_SEXP);
    s += n;
    n = snext(&s);
    if (!n)
      return (GPG_ERR_INV_SEXP);
    s += n;
    if (*s != ')')
      return (GPG_ERR_INV_SEXP);
    s++;
  }
  if (*s != ')')
    return (GPG_ERR_INV_SEXP);
  s++;
  hash_end = s;

  gcry_md_hash_buffer(GCRY_MD_SHA1, sha1hash, hash_begin,
                      hash_end - hash_begin);

  return 0;
}

/* Merge the parameter list contained in CLEARTEXT with the original
 * protect lists PROTECTEDKEY by replacing the list at REPLACEPOS.
 * Return the new list in RESULT and the MIC value in the 20 byte
 * buffer SHA1HASH; if SHA1HASH is NULL no MIC will be computed.
 * CUTOFF and CUTLEN will receive the offset and the length of the
 * resulting list which should go into the MIC calculation but then be
 * removed.  */
static int merge_lists(const unsigned char *protectedkey, size_t replacepos,
                       const unsigned char *cleartext, unsigned char *sha1hash,
                       unsigned char **result, size_t *resultlen,
                       size_t *cutoff, size_t *cutlen) {
  size_t n, newlistlen;
  unsigned char *newlist, *p;
  const unsigned char *s;
  const unsigned char *startpos, *endpos;
  int i, rc;

  *result = NULL;
  *resultlen = 0;
  *cutoff = 0;
  *cutlen = 0;

  if (replacepos < 26)
    return (GPG_ERR_BUG);

  /* Estimate the required size of the resulting list.  We have a large
     safety margin of >20 bytes (FIXME: MIC hash from CLEARTEXT and the
     removed "protected-" */
  newlistlen = gcry_sexp_canon_len(protectedkey, 0, NULL, NULL);
  if (!newlistlen)
    return (GPG_ERR_BUG);
  n = gcry_sexp_canon_len(cleartext, 0, NULL, NULL);
  if (!n)
    return (GPG_ERR_BUG);
  newlistlen += n;
  newlist = gcry_malloc_secure(newlistlen);
  if (!newlist)
    return -99; // out_of_core ();

  /* Copy the initial segment */
  strcpy((char *)newlist, "(11:private-key");
  p = newlist + 15;
  memcpy(p, protectedkey + 15 + 10, replacepos - 15 - 10);
  p += replacepos - 15 - 10;

  /* Copy the cleartext.  */
  s = cleartext;
  if (*s != '(' && s[1] != '(')
    return (GPG_ERR_BUG); /*we already checked this */
  s += 2;
  startpos = s;
  while (*s == '(') {
    s++;
    n = snext(&s);
    if (!n)
      goto invalid_sexp;
    s += n;
    n = snext(&s);
    if (!n)
      goto invalid_sexp;
    s += n;
    if (*s != ')')
      goto invalid_sexp;
    s++;
  }
  if (*s != ')')
    goto invalid_sexp;
  endpos = s;
  s++;

  /* Intermezzo: Get the MIC if requested.  */
  if (sha1hash) {
    if (*s != '(')
      goto invalid_sexp;
    s++;
    n = snext(&s);
    if (!smatch(&s, n, "hash"))
      goto invalid_sexp;
    n = snext(&s);
    if (!smatch(&s, n, "sha1"))
      goto invalid_sexp;
    n = snext(&s);
    if (n != 20)
      goto invalid_sexp;
    memcpy(sha1hash, s, 20);
    s += n;
    if (*s != ')')
      goto invalid_sexp;
  }

  /* Append the parameter list.  */
  memcpy(p, startpos, endpos - startpos);
  p += endpos - startpos;

  /* Skip over the protected list element in the original list.  */
  s = protectedkey + replacepos;
  assert(*s == '(');
  s++;
  i = 1;
  rc = sskip(&s, &i);
  if (rc)
    goto failure;
  /* Record the position of the optional protected-at expression.  */
  if (*s == '(') {
    const unsigned char *save_s = s;
    s++;
    n = snext(&s);
    if (smatch(&s, n, "protected-at")) {
      i = 1;
      rc = sskip(&s, &i);
      if (rc)
        goto failure;
      *cutlen = s - save_s;
    }
    s = save_s;
  }
  startpos = s;
  i = 2; /* we are inside this level */
  rc = sskip(&s, &i);
  if (rc)
    goto failure;
  assert(s[-1] == ')');
  endpos = s; /* one behind the end of the list */

  /* Append the rest. */
  if (*cutlen)
    *cutoff = p - newlist;
  memcpy(p, startpos, endpos - startpos);
  p += endpos - startpos;

  /* ready */
  *result = newlist;
  *resultlen = newlistlen;
  return 0;

failure:
  return rc;

invalid_sexp:
  return (GPG_ERR_INV_SEXP);
}

/* Unprotect the key encoded in canonical format.  We assume a valid
   S-Exp here.  If a protected-at item is available, its value will
   be stored at protected_at unless this is NULL.  */
int agent_unprotect(const unsigned char *protectedkey, const char *passphrase,
                    unsigned char **result, size_t *resultlen) {
  static struct {
    const char *name; /* Name of the protection method. */
    int algo;         /* (A zero indicates the "openpgp-native" hack.)  */
    int keylen;       /* Used key length in bytes.  */
    unsigned int is_ocb : 1;
  } algotable[] = {
      {"openpgp-s2k3-sha1-aes-cbc", GCRY_CIPHER_AES128, (128 / 8)},
      {"openpgp-s2k3-sha1-aes256-cbc", GCRY_CIPHER_AES256, (256 / 8)},
      {"openpgp-s2k3-ocb-aes", GCRY_CIPHER_AES128, (128 / 8), 1},
      {"openpgp-native", 0, 0}};
  int rc;
  const unsigned char *s;
  const unsigned char *protect_list;
  size_t n;
  int infidx, i;
  unsigned char sha1hash[20], sha1hash2[20];
  const unsigned char *s2ksalt;
  unsigned long s2kcount;
  const unsigned char *iv;
  int prot_cipher, prot_cipher_keylen;
  int is_ocb;
  const unsigned char *aad_begin, *aad_end, *aadhole_begin, *aadhole_end;
  const unsigned char *prot_begin;
  unsigned char *cleartext;
  unsigned char *final;
  size_t finallen;
  size_t cutoff, cutlen;

  int *protected_at = NULL; // fake

  if (protected_at)
    *protected_at = 0;

  s = protectedkey;
  if (*s != '(')
    return (GPG_ERR_INV_SEXP);
  s++;
  n = snext(&s);
  if (!n)
    return (GPG_ERR_INV_SEXP);
  if (!smatch(&s, n, "protected-private-key"))
    return (GPG_ERR_UNKNOWN_SEXP);
  if (*s != '(')
    return (GPG_ERR_UNKNOWN_SEXP);
  {
    aad_begin = aad_end = s;
    aad_end++;
    i = 1;
    rc = sskip(&aad_end, &i);
    if (rc)
      return rc;
  }

  s++;
  n = snext(&s);
  if (!n)
    return (GPG_ERR_INV_SEXP);

  for (infidx = 0;
       protect_info[infidx].algo && !smatch(&s, n, protect_info[infidx].algo);
       infidx++)
    ;
  if (!protect_info[infidx].algo)
    return (GPG_ERR_UNSUPPORTED_ALGORITHM);

  /* See wether we have a protected-at timestamp.  */
  protect_list = s; /* Save for later.  */
  if (protected_at) {
    while (*s == '(') {
      prot_begin = s;
      s++;
      n = snext(&s);
      if (!n)
        return (GPG_ERR_INV_SEXP);
      if (smatch(&s, n, "protected-at")) {
        n = snext(&s);
        if (!n)
          return (GPG_ERR_INV_SEXP);
        if (n != 15)
          return (GPG_ERR_UNKNOWN_SEXP);
        memcpy(protected_at, s, 15);
        protected_at[15] = 0;
        break;
      }
      s += n;
      i = 1;
      rc = sskip(&s, &i);
      if (rc)
        return rc;
    }
  }

  /* Now find the list with the protected information.  Here is an
     example for such a list:
     (protected openpgp-s2k3-sha1-aes-cbc
        ((sha1 <salt> <count>) <Initialization_Vector>)
        <encrypted_data>)
   */
  s = protect_list;
  for (;;) {
    if (*s != '(')
      return (GPG_ERR_INV_SEXP);
    prot_begin = s;
    s++;
    n = snext(&s);
    if (!n)
      return (GPG_ERR_INV_SEXP);
    if (smatch(&s, n, "protected"))
      break;
    s += n;
    i = 1;
    rc = sskip(&s, &i);
    if (rc)
      return rc;
  }
  /* found */
  {
    aadhole_begin = aadhole_end = prot_begin;
    aadhole_end++;
    i = 1;
    rc = sskip(&aadhole_end, &i);
    if (rc)
      return rc;
  }
  n = snext(&s);
  if (!n)
    return (GPG_ERR_INV_SEXP);

  /* Lookup the protection algo.  */
  prot_cipher = 0;        /* (avoid gcc warning) */
  prot_cipher_keylen = 0; /* (avoid gcc warning) */
  is_ocb = 0;
  for (i = 0; i < DIM(algotable); i++)
    if (smatch(&s, n, algotable[i].name)) {
      prot_cipher = algotable[i].algo;
      prot_cipher_keylen = algotable[i].keylen;
      is_ocb = algotable[i].is_ocb;
      break;
    }
  if (i == DIM(algotable) || (is_ocb && !OCB_MODE_SUPPORTED))
    return (GPG_ERR_UNSUPPORTED_PROTECTION);

  if (!prot_cipher) /* This is "openpgp-native".  */ // not supported by JtR
  {
    /*
    gcry_sexp_t s_prot_begin;

    rc = gcry_sexp_sscan (&s_prot_begin, NULL,
                          prot_begin,
                          gcry_sexp_canon_len (prot_begin, 0,NULL,NULL));
    if (rc)
      return rc;

    rc = convert_from_openpgp_native (ctrl, s_prot_begin, passphrase, &final);
    gcry_sexp_release (s_prot_begin);
    if (!rc)
      {
        *result = final;
        *resultlen = gcry_sexp_canon_len (final, 0, NULL, NULL);
      }
    return rc;
    */
  }

  if (*s != '(' || s[1] != '(')
    return (GPG_ERR_INV_SEXP);
  s += 2;
  n = snext(&s);
  if (!n)
    return (GPG_ERR_INV_SEXP);
  if (!smatch(&s, n, "sha1"))
    return (GPG_ERR_UNSUPPORTED_PROTECTION);
  n = snext(&s);
  if (n != 8)
    return (GPG_ERR_CORRUPTED_PROTECTION);
  s2ksalt = s;
  s += n;
  n = snext(&s);
  if (!n)
    return (GPG_ERR_CORRUPTED_PROTECTION);
  /* We expect a list close as next, so we can simply use strtoul()
     here.  We might want to check that we only have digits - but this
     is nothing we should worry about */
  if (s[n] != ')')
    return (GPG_ERR_INV_SEXP);

  /* Old versions of gpg-agent used the funny floating point number in
     a byte encoding as specified by OpenPGP.  However this is not
     needed and thus we now store it as a plain unsigned integer.  We
     can easily distinguish the old format by looking at its value:
     Less than 256 is an old-style encoded number; other values are
     plain integers.  In any case we check that they are at least
     65536 because we never used a lower value in the past and we
     should have a lower limit.  */
  s2kcount = strtoul((const char *)s, NULL, 10);
  if (!s2kcount)
    return (GPG_ERR_CORRUPTED_PROTECTION);
  if (s2kcount < 256)
    s2kcount = (16ul + (s2kcount & 15)) << ((s2kcount >> 4) + 6);
  if (s2kcount < 65536)
    return (GPG_ERR_CORRUPTED_PROTECTION);

  s += n;
  s++; /* skip list end */

  n = snext(&s);
  if (is_ocb) {
    if (n != 12) /* Wrong size of the nonce. */
      return (GPG_ERR_CORRUPTED_PROTECTION);
  } else {
    if (n != 16) /* Wrong blocksize for IV (we support only 128 bit). */
      return (GPG_ERR_CORRUPTED_PROTECTION);
  }
  iv = s;
  s += n;
  if (*s != ')')
    return (GPG_ERR_INV_SEXP);
  s++;
  n = snext(&s);
  if (!n)
    return (GPG_ERR_INV_SEXP);

  cleartext = NULL; /* Avoid cc warning. */
  rc = do_decryption(aad_begin, aad_end - aad_begin, aadhole_begin,
                     aadhole_end - aadhole_begin, s, n, passphrase, s2ksalt,
                     s2kcount, iv, is_ocb ? 12 : 16, prot_cipher,
                     prot_cipher_keylen, is_ocb, &cleartext);
  if (rc)
    return rc;

  rc = merge_lists(protectedkey, prot_begin - protectedkey, cleartext,
                   is_ocb ? NULL : sha1hash, &final, &finallen, &cutoff,
                   &cutlen); // dhiru: is this required?
  /* Albeit cleartext has been allocated in secure memory and thus
     xfree will wipe it out, we do an extra wipe just in case
     somethings goes badly wrong. */
  if (rc)
    return rc;

  if (!is_ocb) {
    rc = calculate_mic(final, sha1hash2);
    if (!rc && memcmp(sha1hash, sha1hash2, 20))
      rc = (GPG_ERR_CORRUPTED_PROTECTION);
    if (rc) {
      return rc;
    }
  }

  /* Now remove the part which is included in the MIC but should not
     go into the final thing.  */
  if (cutlen) {
    memmove(final + cutoff, final + cutoff + cutlen,
            finallen - cutoff - cutlen);
    finallen -= cutlen;
  }

  *result = final;
  *resultlen = gcry_sexp_canon_len(final, 0, NULL, NULL);
  return 0;
}

// test driver

#define N 128

char passphrase[N];

int main(int argc, char **argv) {
  size_t size;
  unsigned char *buffer = NULL;
  unsigned char result[40960];
  size_t resulten = 0;
  int ret = -1;
  size_t len = 0;

  if (argc < 2) {
    fprintf(stderr, "Usage: %s <.key file>\n", argv[0]);
    exit(EXIT_FAILURE);
  }

  FILE *fp = fopen(argv[1], "rb");
  if (!fp) {
    perror("fopen");
    exit(EXIT_FAILURE);
  }
  fseek(fp, 0L, SEEK_END);
  size = ftell(fp);
  buffer = (unsigned char *)malloc(size);
  if (!buffer) {
    perror("malloc");
    exit(EXIT_FAILURE);
  }

  fseek(fp, 0L, SEEK_SET);
  if (fread(buffer, size, 1, fp) != 1) {
    perror("fread");
    exit(EXIT_FAILURE);
  }

  while (fgets(passphrase, N - 1, stdin) != NULL) {
    len = strlen(passphrase);
    passphrase[len - 1] = 0;

    ret = agent_unprotect(buffer, passphrase, (unsigned char **)&result,
                          &resulten);
    if (ret == 0) {
      printf("Found password: %s\n", passphrase);
      exit(EXIT_SUCCESS);
    }
  }

  exit(EXIT_FAILURE);
}
