CC=gcc
CFLAGS=-lpthread -lcrypto
RM=rm -f

NAME=hashcrack
OBJS=hashcrack.o

SRCDIR=./src
DEFINES=-DPWFILE=\"examples/etc-passwd.txt\" -DLOGFILE=\"log.txt\" -DDICTFILE=\"/usr/share/dict/words\"

all: ${OBJS}
	${CC} ${OBJS} ${CFLAGS} ${DEFINES} -o ${NAME}

%.o: ${SRCDIR}/%.c
	${CC} $< ${CFLAGS} ${DEFINES} -c

clean:
	-${RM} ${OBJS} ${NAME}
