#include <stdio.h>
#include <stdbool.h>

static inline void write_mscratch(unsigned int value){
	asm volatile ("csrw mscratch, %0" :: "r"(value));
}

static inline unsigned int read_mscratch(){
	unsigned int data;
	asm volatile ("csrr %0, mscratch" : "=r"(data));
	return data;
}

static bool verify(unsigned int data){
	unsigned int read_val;
	write_mscratch(data);
	read_val = read_mscratch();
	if(read_val != data){
		printf("\t ERROR: Expected -> 0x%08X  Read: 0x%08X\n",data, read_val);
        return false;
	}
	return true;
}

//test_walking_bits 
static bool walking_bit_1(void) {
    for (unsigned int bit = 1; bit != 0; bit <<= 1) {
        if (!verify(bit)) {
            printf("\t\tERROR: walking bit at 0x%08X\n", bit);
            return false;
        }
    }
    return true;
}
		

	
int main(){
	unsigned int data;
	
	printf("\t [RUN ] TEST1: all zeros  \n");
	data = 0x00000000;
	bool test1 = verify(data);

	printf("\t [RUN ] TEST2: all ones   \n");
	data = 0xFFFFFFFF;
	bool test2 = verify(data);

	printf("\t [RUN ] TEST3: alternating 1010... and 010101...     \n");
	data = 0xAAAAAAAA;
	bool test3a = verify(data);

	data = 0x55555555;
    bool test3b = verify(data);
	
	// Walking 1-bit test for CSR mscratch.
	// Verifies each bit can be set and read independently.
	printf("\t [RUN ] TEST4: walking bit 1  \n");
	bool test4 = walking_bit_1();


	printf("\n--- Test Results ---\n");
    printf("\tAll zeros: %s\n", test1 ? "PASS" : "FAIL");
    printf("\tAll ones: %s\n", test2 ? "PASS" : "FAIL");
    printf("\tAlternating: %s\n", (test3a && test3b) ? "PASS" : "FAIL");
    printf("\tWalking bit: %s\n", test4 ? "PASS" : "FAIL");

	bool overall = test1 && test2 && test3a && test3b && test4;
    
    printf("\n\t [RESULT] %s \n", overall ? "PASS" : "FAIL");
	
	return 0;	

}
	
