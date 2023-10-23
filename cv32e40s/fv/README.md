# Formal Verification

This directory is for running formal property checking.

Read the Makefile for more info.


## Usage Examples

Simple example:
```
make jg
```

Advanced examples:
```
make  jg  USER_DEFINES=+define+MYDEFINE  USER_INCDIRS=+incdir+MYINCDIR
make  jg  JG_EXTRAS=""
make  jg  USER_DEFINES=+define+COREV_ASSERT_OFF
make  jg  USER_DEFINES=+define+DEFONE+DEFTWO+DEFTHREE
```
