/*
 * hashcrack.c
 *
 * [description]
 *
 * The MIT License (MIT)
 * 
 * Copyright (c) 2014 Ben Hamlin
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 *                       __        __             
 *     ____  _________  / /_____  / /_  ___  ____ 
 *    / __ \/ ___/ __ \/ __/ __ \/ __ \/ _ \/ __ \
 *   / /_/ / /  / /_/ / /_/ /_/ / /_/ /  __/ / / /
 *  / .___/_/   \____/\__/\____/_.___/\___/_/ /_/ 
 * /_/      
 *
 */

#include <errno.h>
#include <pthread.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <openssl/sha.h>

#define FORKS (4)
#define ALLOC (40)

/* Defs for a table of digests / usernames. */
#define DIGSZ (20)
#define TABSZ (65536) /* UINT16_MAX + 1 */
#define IDXS_PER_DIG (10)
typedef uint16_t idx_t;

/* Entry in a table of passwd entries. If collisions, occur, instead stores a pointer to a sub-table. */
typedef struct pwent_st
{
  struct pwent_st **next_level;
  char **names;
  int namesz;
  uint8_t dig[DIGSZ];
} pwent;

/* Struct full of info needed by a pthread. */
typedef struct ptinfo_st
{
  pwent **tab;
  FILE *dfp;
  FILE *ofp;
  time_t start;
  int cnt;
} ptinfo;

/*
 * Print an error message and exit().
 */
void error(char *who, int err, int ret) {fprintf(stderr, err ? "%s: %s\n" : "%s\n", who, strerror(err)); exit(ret);}

/*
 * Convert a hexidecimal hash of size (DIGSZ * 2) into a (pre-allocated) digest of size DIGSZ.
 */
static inline void hash2dig(char *h, uint8_t *d)
{
  char byte[3] = "00";

  for(; *h; ++d, h += 2)
  {
    memcpy(byte, h, 2);
    *d = strtol(byte, NULL, 0x10);
  }
}

/*
 * Parse the passwd file in fp, which is assumed to be open and correctly formatted.
 * Assume *name and *dig are NULL. Return 0 on succes, nonzero on failure.
 */
static inline int fake_getpwent(char **namep, uint8_t *dig, FILE *fp)
{
  char hash[(DIGSZ * 2) + 1];
  size_t namesz = 0;
  *namep = NULL;

  /* Read the next name from fp. */
  if(getdelim(namep, &namesz, '\t', fp) < 0) {free(*namep); return EOF;};
  (*namep)[strlen(*namep) - 1] = '\0';

  /* Read the next hash from fp. */
  if(!(fgets(hash, (DIGSZ * 2) + 1, fp))) error("fgets()", errno, errno);
  if(getc(fp) != '\n') error("Found a hash of abnormal size!", 0, 1);

  /* Convert the hash to a digest. */
  hash2dig(hash, dig);

  #ifdef DEBUG
    int i;
    printf("fake_getpwent():\tname: %s\n\t\t\thash: %s\n\t\t\tdig: ", *namep, hash);
    for(i = 0; i < DIGSZ; ++i) printf("%02x", (dig)[i]); puts("");
  #endif

  return 0;
}

/*
 * Fill the pwent struct in entp with name, as well as dig, if it's unique.
 * Return 0 if we successfully added. Return 1 if we need to go deeper.
 */
int pwentadd(pwent **entpp, char *name, uint8_t *dig)
{
  pwent *entp = *entpp;
  int i = 0;

  /* if *entpp is empty, create a new pwent and add our data. */
  if(!entp)
  {
    if(!(entp = (*entpp = malloc(sizeof(pwent))))) error("malloc()", errno, errno);
    entp->next_level = NULL;
    if(!(entp->names = malloc(ALLOC * sizeof(char*)))) error("malloc()", errno, errno);
    memset(entp->names, 0, ALLOC * sizeof(char*));
    entp->namesz = ALLOC;
    entp->names[0] = name;
    memcpy(entp->dig, dig, DIGSZ * (sizeof *dig));
  }
  /* If the hash already exists, add our name to the list. */
  else if(!entp->next_level && !memcmp(entp->dig, dig, DIGSZ))
  {
    for(i = 0; entp->names[i]; ++i);
    if(i >= entp->namesz - 1)
    {
      if(!(entp->names = realloc(entp->names, (entp->namesz + ALLOC) * sizeof(char*))))
        error("realloc()", errno, errno);
      memset(entp->names + entp->namesz, 0, ALLOC * sizeof(char*));
      entp->namesz += ALLOC;
    }
    entp->names[i] = name;
  }
  /* Otherwise we need to go deeper. */
  else return 1;

  #ifdef DEBUG
    printf("pwentadd():\t\tname: %s\n\t\t\t\tidx: %d\n", name, i);
  #endif

  return 0;
}

/*
 * Store dig and uid in tab. Assume tab is pre-allocated with TABSZ pwent*s.
 */
void tabadd(pwent **tab, uint8_t *dig, char *name)
{
  idx_t *idxs = (idx_t*)dig, idx;
  int i, tempnamesz;
  uint8_t *tempdig;
  char **tempnames;

  /* Traverse down levels of the table until we find somewhere to add. */
  for(i = 0, idx = idxs[0]; i < IDXS_PER_DIG; idx = idxs[++i])
    /* Add at this level if we can. */
    if(!pwentadd(tab + idx, name, dig)) break;
    /* Otherwise, we need to go deeper. */
    else
    {
      if(tab[idx]->next_level) tab = tab[idx]->next_level;
      else
      {
        /* Store the old pwent. */
        tempdig = tab[idx]->dig;
        tempnames = tab[idx]->names;
        tempnamesz = tab[idx]->namesz;

        /* Create a new level. */
        if(!(tab[idx]->next_level = malloc(TABSZ * sizeof(pwent*)))) error("malloc()", errno, errno);
        tab = tab[idx]->next_level;
        memset(tab, 0, TABSZ * (sizeof (pwent*)));

        /* Copy the previously stored digest down. */
        idx = ((idx_t*)tempdig)[i + 1];
        if(!(tab[idx] = malloc(sizeof(pwent)))) error("malloc()", errno, errno);
        tab[idx]->next_level = NULL;
        memcpy(tab[idx]->dig, tempdig, DIGSZ * (sizeof *dig));
        tab[idx]->names = tempnames;
        tab[idx]->namesz = tempnamesz;
      }
    }   /* ...and try again wth the next table/index. */

  #ifdef DEBUG
    printf("tabadd():\t\tname: %s\n\t\t\tadded at: level %d, index %x\n", name, i + 1, idx);
  #endif
}

/*
 * Recursively free tab.
 */
int tabfree(pwent **tab)
{
  int i, j;

  if(!tab) return 0;

  for(i = 0; i < TABSZ; ++i)
    if(tab[i])
    {
      if(!tabfree(tab[i]->next_level))
      {
        for(j = 0; tab[i]->names[j]; ++j) free(tab[i]->names[j]);
        free(tab[i]->names);
        free(tab[i]);
      }
    }

  free(tab);

  return 1;
}

/*
 * Parse PWFILE. Return an array of usernames
 */
pwent **parse_passwd(char *pwfile)
{
  pwent **tab;
  uint8_t dig[DIGSZ];
  char *name;
  FILE *fp;

  if(!(fp = fopen(pwfile, "r"))) error("fopen()", errno, errno);

  if(!(tab = malloc(TABSZ * sizeof(pwent*)))) error("malloc()", errno, errno);
  memset(tab, 0, TABSZ * sizeof(pwent*));

  /* Get pwents and add them to the hash table. */
  while(fake_getpwent(&name, dig, fp) >= 0)
    /* Store the uid and digest in the table. */
    tabadd(tab, dig, name);

  fclose(fp);

  return tab;
}

/*
 * Check a password against the hash table. return the list of names if we have a match, or NULL;
 */
static inline char **pwchk(pwent **tab, char *pw, size_t pwlen)
{
  uint8_t dig[DIGSZ];
  register idx_t *idxp;

  if(!SHA1((uint8_t*)pw, pwlen, dig)) error("SHA1()", errno, errno);

  for(idxp = (idx_t*)dig; tab[*idxp]; ++idxp)
  {
    if(!tab[*idxp]->next_level)
      if(!memcmp(tab[*idxp]->dig, dig, DIGSZ * sizeof(uint8_t)))
      {
        return tab[*idxp]->names;
      }
      else return NULL;
    else tab = tab[*idxp]->next_level;
  }

  return NULL;
}

/*
 * Parse a dictionary file (newline separated list of words) and test each entry aginst tab.
 */
void *parse_dict(void *p)
{
  ptinfo *pti = p;
  char rpw[256], *pw = rpw + 1, **matches,
       punct[] = "!@$%^&*()-=_+{}[]|\\:<>,.?/1234567890";
  int punctlen = (sizeof punct) - 1, pwlen, rpwlen, i, j;

  while(fgets(rpw + 1, sizeof rpw, pti->dfp))
  {
    pwlen = strlen(rpw + 1);
    if((rpw[pwlen] != '\n')) ++pwlen;
    rpw[pwlen + 1] = '\0';
    pw = rpw + 1;

    for(i = punctlen, rpw[pwlen] = punct[i]; i >= 0; rpw[pwlen] = punct[--i])
    {
      rpwlen = strlen(pw);
      if((matches = pwchk(pti->tab, pw, rpwlen)))
        for(; *matches; ++matches)
          fprintf(pti->ofp, "%lu\t%d\t\%s\t%s\n", time(0) - pti->start, ++pti->cnt, *matches, pw);
    }
    for(i = punctlen - 1, rpw[0] = punct[i], --pw, ++rpwlen; i >= 0; rpw[0] = punct[--i])
    {
      for(j = punctlen, rpw[pwlen] = punct[j]; j >= 0; rpw[pwlen] = punct[--j])
      {
        if((matches = pwchk(pti->tab, pw, rpwlen)))
          for(; *matches; ++matches)
            fprintf(pti->ofp, "%lu\t%d\t\%s\t%s\n", time(0) - pti->start, ++pti->cnt, *matches, pw);
      }
    }
  }

  return NULL;
}

int main()
{
  int i;
  pthread_t pts[4];
  ptinfo pti;
  pti.start = time(0);
  pti.cnt = 0;

  pti.tab = parse_passwd(PWFILE);

  if(!(pti.dfp = fopen(DICTFILE, "r"))) error("fopen()", errno, errno);
  if(!(pti.ofp = fopen(LOGFILE, "w"))) error("fopen()", errno, errno);

  for(i = 0; i < FORKS; ++i)
    pthread_create(pts + i, NULL, parse_dict, &pti);

  for(i = 0; i < FORKS; ++i)
    pthread_join(pts[i], NULL);

  fclose(pti.dfp);
  fclose(pti.ofp);
  tabfree(pti.tab);

  return 0;
}
