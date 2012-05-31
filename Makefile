
CC = gcc
CFLAGS = -ansi -pedantic
CFLAGS += -Wall -Wextra -Wstrict-aliasing
CFLAGS += -g
#CFLAGS += -O3

IFLAGS = -I$(cx_path)/..

cx_path = ../cx
bin_path = ../bin

exe_list = eva
exe_list := $(addprefix $(bin_path)/,$(exe_list))

all: $(exe_list)

cx_obj_list = fileb.o sys-cx.o
cx_obj_list := $(addprefix $(cx_path)/,$(cx_obj_list))

$(bin_path)/eva: eva.o $(cx_obj_list)
	$(CC) $(CFLAGS) -o $@ $^

$(exe_list): | $(cx_path)

.PHONY: $(cx_path)
$(cx_path):
	$(MAKE) -C $(cx_path)

%.o: %.c
	$(CC) -c $(CFLAGS) $(IFLAGS) $^ -o $@

$(exe_list): | $(bin_path)

$(bin_path):
	mkdir -p $(bin_path)

.PHONY: clean
clean:
	rm -f *.o $(exe_list)

