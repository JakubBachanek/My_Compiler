OBJECTS = parser.o lexer.o code.o
FLAGS = -Wall -Wextra -pedantic

kompilator: ${OBJECTS} Makefile
	g++ ${FLAGS} -o kompilator ${OBJECTS}

parser.o: k.y
	bison -Wall -o k_y.c -d k.y
	g++ -c ${FLAGS} -o parser.o k_y.c

lexer.o: k.lex k_y.h
	flex -o k_l.c k.lex
	g++ -c ${FLAGS} -o lexer.o k_l.c

code.o: k_lib.h k.cpp
	g++ -c ${FLAGS} -o code.o k.cpp -lm

clean:
	rm -f k_y.c k_l.c k_y.h ${OBJECTS}
