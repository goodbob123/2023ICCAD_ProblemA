PP := g++
CC := gcc
CFLAGS := -g
LDFLAGS = -lm -ldl -lreadline -lpthread

INC = -I ./kissat_extras/src

TARGET := main

.PHONY: all clean

all: $(TARGET)

$(TARGET): main.o ./libkissat.a 
	$(PP) $(CFLAGS) -o $(TARGET) ./main.o $(LDFLAGS) -L. -lkissat

main.o: main.cpp 
	$(PP) $(CFLAGS) -std=c++11 $(INC) -c main.cpp -o main.o 

clean:
	rm -rf $(TARGET) *.o
