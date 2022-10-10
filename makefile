# ----------------------------
# Makefile Options
# ----------------------------

NAME = CASYMBA
ICON = icon.png
DESCRIPTION = "CASymba"
COMPRESSED = YES
ARCHIVED = YES

CFLAGS = -Wall -Wextra -Oz
CXXFLAGS = -Wall -Wextra -Oz

# ----------------------------

include $(shell cedev-config --makefile)
