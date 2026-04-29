CC      = gcc
CFLAGS  = -Wall -Wextra -O2 -std=c11 -D_GNU_SOURCE $(shell python3-config --includes)
LDFLAGS = $(shell python3-config --ldflags --embed)
TARGET  = node

.PHONY: all clean

all: $(TARGET)

$(TARGET): node.c diffusion.c scheduler_bridge.c node.h scheduler_bridge.h cJSON.c cJSON.h
	$(CC) $(CFLAGS) -o $@ node.c diffusion.c scheduler_bridge.c cJSON.c $(LDFLAGS) -lm -lssl -lcrypto

clean:
	rm -f $(TARGET)
