
CC = gcc
CFLAGS =
CFLAGS += -g
#CFLAGS += -O3
CFLAGS += -ansi -pedantic
CFLAGS += -Wall -Wextra -Wstrict-aliasing

cx_path = ../cx
bin_path = ../bin

IFLAGS = -I..

CFLAGS += $(IFLAGS)

exe_list = eva pipelisp
exe_list := $(addprefix $(bin_path)/,$(exe_list))

all: $(exe_list)

cx_obj_list = fileb.o syscx.o
cx_obj_list := $(addprefix $(cx_path)/,$(cx_obj_list))

$(bin_path)/eva: eva.o $(cx_obj_list)
	$(CC) $(CFLAGS) -o $@ $^

$(bin_path)/pipelisp: pipelisp.o $(cx_obj_list)
	$(CC) $(CFLAGS) -o $@ $^

%.o: %.c
	$(CC) -c $(CFLAGS) $^ -o $@

$(exe_list): | $(bin_path)

$(bin_path):
	mkdir -p $(bin_path)

.PHONY: clean
clean:
	rm -f *.o $(cx_path)/*.o $(exe_list)

