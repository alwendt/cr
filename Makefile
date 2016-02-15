CFLAGS=-g -pg

.c.o: ;	$(CC) $(CFLAGS) -c $*.c
cr:	cr.o int.o prioq.o  
	$(CC) -pg -g -o cr cr.o int.o prioq.o \
		regexp/regexp.o regexp/regsub.o regexp/regerror.o

ocr.o:	cr.c
	$(CC) -S -O cr.c
	/usr/wendt/bin/copt <cr.s rmr11.copt | /usr/wendt/bin/copt fixr11.copt | /usr/wendt/bin/copt resr11.copt | /usr/wendt/bin/cr cr.ridge >ocr.s 
	$(CC) -c ocr.s

ocr:	ocr.o int.o prioq.o index.o 
	$(CC) -o ocr ocr.o int.o prioq.o index.o 
	
crgprof.o:	cr.c
	$(CC) -c -gp cr.c
	mv cr.o crgprof.o

intgprof.o:	int.c
	$(CC) -c -gp int.c
	mv int.o intgprof.o

prioqgprof.o:	prioq.c
	$(CC) -c -gp prioq.c
	mv prioq.o prioqgprof.o

crgprof: crgprof.o intgprof.o prioqgprof.o
	ld -o crgprof /usr/lib/gcrt0.o crgprof.o intgprof.o prioqgprof.o -lc_p

crprof.o:	cr.c
	$(CC) -c -p cr.c
	mv cr.o crprof.o

intprof.o:	int.c
	$(CC) -c -p int.c
	mv int.o intprof.o

prioqprof.o:	prioq.c
	$(CC) -c -p prioq.c
	mv prioq.o prioqprof.o

crprof: crprof.o intprof.o prioqprof.o
	$(CC) -p -o crprof crprof.o intprof.o prioqprof.o

mkpat:	balloc.o hash.o itop.o mkpat.o
	$(CC) -o mkpat balloc.o hash.o itop.o mkpat.o
