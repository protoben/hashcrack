#include <errno.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <openssl/sha.h>

#define LOGFILE "log-m3.txt"
#define PWFILE "sha1-salted.txt"
#define DICTFILE "/usr/share/dict/words"
#define PROCS (5)
#define ALLOC (10)

/* Defs for a table of digests / usernames. */
#define SALTSZ (8)
#define DIGSZ (20)
#define SALTDIGSZ (28)
#define TABSZ (65536) /* UINT16_MAX + 1 */
#define IDXS_PER_DIG (14)
typedef uint16_t idx_t;

/* Entry in a table of passwd entries. If collisions, occur, instead stores a pointer to a sub-table. */
typedef struct pwent_st
{
  struct pwent_st **next_level;
  char **names;
  int namesz;
  uint8_t saltdig[SALTDIGSZ];
} pwent;

/* Node in a salt list. */
typedef struct snode_st
{
  uint8_t *sdig;
  struct snode_st *next;
} snode;

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
 * Convert a hexidecimal salt of size (SALTSZ * 2) into a (pre-allocated) salt digest of size SALTSZ.
 */
static inline void salt2sdig(char *s, uint8_t *sd)
{
  char byte[3] = "00";

  for(; *s; ++sd, s += 2)
  {
    memcpy(byte, s, 2);
    *sd = strtol(byte, NULL, 0x10);
  }
}

/*
 * Parse the passwd file in fp, which is assumed to be open and correctly formatted.
 */
static inline int fake_getpwent(char **namep, uint8_t *saltdig, FILE *fp)
{
  char *salt = NULL, hash[(DIGSZ * 2) + 1];
  size_t namesz = 0, saltsz = 0;
  *namep = NULL;

  /* Read the next name from fp. */
  if(getdelim(namep, &namesz, '\t', fp) < 0) {free(*namep); return EOF;}
  (*namep)[strlen(*namep) - 1] = '\0';

  /* Read the next hash from fp. */
  if(getdelim(&salt, &saltsz, '\t', fp) < 0) error("Incomplete final entry!", 0, 1);
  salt[strlen(salt) - 1] = '\0';

  /* Convert the hash to a digest. */
  salt2sdig(salt, saltdig);

  /* Read the next salt from fp. */
  if(!(fgets(hash, (DIGSZ * 2) + 1, fp))) error("fgets()", errno, errno);
  if(getc(fp) != '\n') error("Found a hash of abnormal size!", 0, 1);

  /* Convert the hash to a digest. */
  hash2dig(hash, saltdig + SALTSZ);

  #ifdef DEBUG
    int i;
    printf("fake_getpwent():\tname: %s\n\t\t\thash: %s\n\t\t\tsalt: %s\n\t\t\tsaltdig: ", *namep, hash, salt);
    for(i = 0; i < SALTDIGSZ; ++i) printf("%02x", (saltdig)[i]); puts("");
  #endif

  return 0;
}

/*
 * Add a salt at sdig to the salt list pointed to by head if the first chunk is not indexed in tab.
 */
static inline void saltadd(uint8_t *sdig, snode **headp, pwent **tab)
{
  snode *temp;

  /* If the first idx_t of sdig is already in the table, we don't need to add it. */
  if(tab[*((idx_t*)sdig)]) return;

  /* Otherwise, add it at the head of the list. */
  temp = *headp;
  (*headp) = malloc(sizeof(snode));
  (*headp)->next = temp;
  temp = *headp;
  temp->sdig = malloc(SALTSZ);
  memcpy(temp->sdig, sdig, SALTSZ);

  #ifdef DEBUG
    int i;
    puts("saltadd():\t\t");
    for(i = 0; i < SALTSZ; ++i) printf("%02x", sdig[i]); puts("");
  #endif
}

/*
 * Fill the pwent struct in entp with name, as well as dig, if it's unique.
 * Return 0 if we successfully added. Return 1 if we need to go deeper.
 */
int pwentadd(pwent **entpp, char *name, uint8_t *saltdig)
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
    memcpy(entp->saltdig, saltdig, SALTDIGSZ * sizeof(uint8_t));
  }
  /* If the hash already exists, add our name to the list. */
  else if(!entp->next_level && !memcmp(entp->saltdig, saltdig, SALTDIGSZ))
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
void tabadd(pwent **tab, uint8_t *sdig, char *name)
{
  idx_t *idxs = (idx_t*)sdig, idx;
  int i, tempnamesz;
  uint8_t *tempsdig;
  char **tempnames;

  /* Traverse down levels of the table until we find somewhere to add. */
  for(i = 0, idx = idxs[0]; i < IDXS_PER_DIG; idx = idxs[++i])
    /* Add at this level if we can. */
    if(!pwentadd(tab + idx, name, sdig)) break;
    /* Otherwise, we need to go deeper. */
    else
    {
      if(tab[idx]->next_level) tab = tab[idx]->next_level;
      else
      {
        /* Store the old pwent. */
        tempsdig = tab[idx]->saltdig;
        tempnames = tab[idx]->names;
        tempnamesz = tab[idx]->namesz;

        /* Create a new level. */
        if(!(tab[idx]->next_level = malloc(TABSZ * sizeof(pwent*)))) error("malloc()", errno, errno);
        tab = tab[idx]->next_level;
        memset(tab, 0, TABSZ * (sizeof(pwent*)));

        /* Copy the previously stored digest down. */
        idx = ((idx_t*)tempsdig)[i + 1];
        if(!(tab[idx] = malloc(sizeof(pwent)))) error("malloc()", errno, errno);
        tab[idx]->next_level = NULL;
        memcpy(tab[idx]->saltdig, tempsdig, SALTDIGSZ * (sizeof(uint8_t)));
        tab[idx]->names = tempnames;
        tab[idx]->namesz = tempnamesz;
      }
    }   /* ...and try again wth the next table/index. */

  #if DEBUG >= 2
    printf("tabadd():\t\tname: %s\n\t\t\tadded at: level %d, index %x\n", name, i + 1, idx);
  #endif
}

/*
 * Determine whether dig is in tab. Return associated names array if so, otherwise, NULL.
 */
static inline char **tabchk(pwent **tab, uint8_t *sdig)
{
  register idx_t *idxs = (idx_t*)sdig, idx;
  register int i;

  /* Traverse down the table looking for the digest to check. */
  for(i = 0, idx = idxs[0]; i < IDXS_PER_DIG; idx = idxs[++i])
    /* Welp, nothing here, turns out. */
    if(!tab[idx]) return NULL;
    /* We've found the digest to check. */
    else if(!tab[idx]->next_level)
    {
      if(!(memcmp(tab[idx]->saltdig, sdig, DIGSZ * (sizeof *sdig)))) return tab[idx]->names;
      else return NULL;
    }
    /* We need to go deeper. */
    else tab = tab[idx]->next_level;

  /* Should never get here. */
  fputs("tabchk() overran table!", stderr);
  return NULL;
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
 * Free the salt list pointed to by head.
 */
void slistfree(snode *head)
{
  snode *temp;

  while(head)
  {
    temp = head;
    head = head->next;
    free(temp->sdig);
    free(temp);
  }
}

/*
 * Parse PWFILE. Return an array of usernames
 */
pwent **parse_passwd(char *pwfile, snode **headp)
{
  pwent **tab;
  uint8_t saltdig[SALTDIGSZ];
  char *name;
  FILE *fp;

  if(!(fp = fopen(pwfile, "r"))) error("fopen()", errno, errno);

  if(!(tab = malloc(TABSZ * sizeof(pwent*)))) error("malloc()", errno, errno);
  memset(tab, 0, TABSZ * sizeof(pwent*));

  /* Get pwents and add them to the hash table. */
  while(fake_getpwent(&name, saltdig, fp) >= 0)
  {
    /* Store the salt in the salt list. */
    saltadd(saltdig, headp, tab);
    /* Store the uid and digest in the table. */
    tabadd(tab, saltdig, name);
  }

  fclose(fp);

  return tab;
}

/*
 * Check a password against the hash table. return the list of names if we have a match, or NULL;
 */
static inline char **pwchk(pwent **tab, char *pw, uint8_t *sdig)
{
  uint8_t saltdig[SALTDIGSZ];
  register idx_t *idxp;
  SHA_CTX c;

  memcpy(saltdig, sdig, SALTSZ);

  //if(!SHA1((uint8_t*)pw, strlen(pw), saltdig + SALTSZ)) error("SHA1()", errno, errno);
  SHA1_Init(&c);
  SHA1_Update(&c, pw, strlen(pw));
  SHA1_Update(&c, sdig, SALTSZ);
  SHA1_Final(saltdig + SALTSZ, &c);



  for(idxp = (idx_t*)saltdig; tab[*idxp]; ++idxp)
  {
    if(!tab[*idxp]->next_level)
      if(!memcmp(tab[*idxp]->saltdig, saltdig, SALTDIGSZ * sizeof(uint8_t)))
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
void parse_dict(FILE *fp, pwent **tab, time_t start, snode *head)
{
  char *pw = NULL, **matches;
  size_t pwsz = 0;
  int pwlen, cnt = 0;
  FILE *ofp;
  snode *temp;

  if(!(ofp = fopen(LOGFILE, "w"))) error("fopen()", errno, errno);

  while((pwlen = getline(&pw, &pwsz, fp)) > 0)
  {
    pw[--pwlen] = '\0';
    temp = head;
    while(temp)
    {
      if((matches = pwchk(tab, pw, temp->sdig)))
        for(; *matches; ++matches) fprintf(ofp, "%lu\t%d\t\%s\t%s\n", time(0) - start, ++cnt, *matches, pw);
      temp = temp->next;
    }
  }

  free(pw);
  fclose(ofp);
}

int main()
{
  pwent **tab;
  snode *head = NULL;
  FILE *dfp;
  time_t start = time(0);

  tab = parse_passwd(PWFILE, &head);

  if(!(dfp = fopen(DICTFILE, "r"))) error("fopen()", errno, errno);

  parse_dict(dfp, tab, start, head);
  fclose(dfp);

  slistfree(head);
  tabfree(tab);

  return 0;
}
