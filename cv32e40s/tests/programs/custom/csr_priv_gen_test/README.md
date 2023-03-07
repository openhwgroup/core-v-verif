Contains generated tests on U-mode csr instructions to insert illegall access

Needs `CFG=pmp` for allowing U-mode to run.


# Python generator files

## Motivation
Runing through the test-plan it became apparant at some point that it would be necessary to have tests which contained a number of instructions to satisfy testing goals. The solution became python scripts which use string manipulation to generate these instructions directly to the relevant .h and .S files in the directory.

## Function
The script works by looping through the given file (see the top of the file .py file for name declarations) line by line until a 'trigger' string is reached, usually this string can look something like this:

```
// start of generated code
```

And everything below this line is then overwritten.

The script will either have a list called 'reg_string' which is a manually constructed list fetched from a table in the RISC specification. The file will then parse this registry list and create ranges to include all registries within the list. It then writes instructions for that registry to file. Which instructions are based on the test plan.

Afterwards it searches through the header file and changes the 'ILLEGALLY_GENERATED_INSN' define, which is what both the .S and .c files use when sanity checking or asserting that the number of trapped instructions matches what's been generated. There is also some info printed to the terminal about how many lines and which files are written to.


## Maintenance
The scripts are intended to be easily maintenable (although I guess time will tell), and therefore the generation of the instructions themselves are kept within 'generator()' functions and marked variables. If there's a need to change the number of registries, the types of instructions etc. these are found there. Afterwards you should be able to run the script and it will properly update the instructions for you.
