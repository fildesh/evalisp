
default: all

CC = gcc

CONFIG += ansi
CONFIG += debug

IFLAGS = -I..

CFLAGS += $(IFLAGS)

CxPath = ../cx
BinPath = ../bin
PfxBldPath = ../eva-bld
BldPath = $(PfxBldPath)/eva
CxBldPath = $(PfxBldPath)/cx

ExeList = eva pipelisp
Deps := $(ExeList)
ExeList := $(addprefix $(BinPath)/,$(ExeList))
Objs = $(addprefix $(BldPath)/,$(addsuffix .o,$(Deps)))

include $(CxPath)/include.mk

all: $(ExeList)

$(BinPath)/eva: $(BldPath)/eva.o \
	$(addprefix $(CxBldPath)/,fileb.o sxpn.o syscx.o)
	$(CC) $(CFLAGS) -o $@ $^

$(BinPath)/pipelisp: $(BldPath)/pipelisp.o \
	$(addprefix $(CxBldPath)/, fileb.o syscx.o)
	$(CC) $(CFLAGS) -o $@ $^

.PHONY: clean
clean:
	rm -fr $(PfxBldPath)
	rm -f $(ExeList)

