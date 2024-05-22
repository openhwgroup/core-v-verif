#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>

#include "custom_interrupt_test.h"

volatile uint32_t irq_id                  = 0;
volatile uint32_t irq_id_q[IRQ_NUM];
volatile uint32_t irq_id_q_ptr            = 0;
volatile uint32_t mmcause                 = 0;
volatile uint32_t active_test             = 0;
volatile uint32_t nested_irq              = 0;
volatile uint32_t nested_irq_valid        = 0;
volatile uint32_t in_direct_handler       = 0;
volatile uint32_t event;
volatile uint32_t num_taken_interrupts;

volatile uint32_t IRQ_ID_PRIORITY [IRQ_NUM] = {
    FAST15_IRQ_ID   ,
    FAST14_IRQ_ID   ,
    FAST13_IRQ_ID   ,
    FAST12_IRQ_ID   ,
    FAST11_IRQ_ID   ,
    FAST10_IRQ_ID   ,
    FAST9_IRQ_ID    ,
    FAST8_IRQ_ID    ,
    FAST7_IRQ_ID    ,
    FAST6_IRQ_ID    ,
    FAST5_IRQ_ID    ,
    FAST4_IRQ_ID    ,
    FAST3_IRQ_ID    ,
    FAST2_IRQ_ID    ,
    FAST1_IRQ_ID    ,
    FAST0_IRQ_ID    ,
    EXTERNAL_IRQ_ID ,
    SOFTWARE_IRQ_ID ,
    TIMER_IRQ_ID
};

// FIXME: Create VP register for a timer on reliable time-base (i.e. cpu clock)
// FIXME: Add to common infrastructure
void delay(int count) {
    for (volatile int d = 0; d < count; d++);
}

void mstatus_mie_enable() {
    volatile int mie_bit = 0x1 << MSTATUS_MIE_BIT;
    __asm__ volatile("csrrs x0, mstatus, %0" : : "r" (mie_bit));
}

void mstatus_mie_disable() {
    volatile int mie_bit = 0x1 << MSTATUS_MIE_BIT;
    __asm__ volatile("csrrc x0, mstatus, %0" : : "r" (mie_bit));
}

void mie_enable_all() {
    volatile uint32_t mie_mask = (uint32_t) -1;
    __asm__ volatile("csrrs x0, mie, %0" : : "r" (mie_mask));
}

void mie_disable_all() {
    volatile uint32_t mie_mask = (uint32_t) -1;
    __asm__ volatile("csrrc x0, mie, %0" : : "r" (mie_mask));
}

void mie_enable(uint32_t irq) {
    // Enable the interrupt irq in MIE
    volatile uint32_t mie_bit = 0x1 << irq;
    __asm__ volatile("csrrs x0, mie, %0" : : "r" (mie_bit));
}

void mie_disable(uint32_t irq) {
    // Disable the interrupt irq in MIE
    volatile uint32_t mie_bit = 0x1 << irq;
    __asm__ volatile("csrrc x0, mie, %0" : : "r" (mie_bit));
}

void mm_ram_assert_irq(uint32_t mask, uint32_t cycle_delay) {
    *TIMER_REG_ADDR = mask;
    *TIMER_VAL_ADDR = 1 + cycle_delay;
}

uint32_t random_num(uint32_t upper_bound, uint32_t lower_bound) {
    volatile uint32_t random_num = *((volatile int *) CV_VP_RANDOM_NUM_BASE);
    volatile uint32_t num = (random_num  % (upper_bound - lower_bound + 1)) + lower_bound;
    return num;
}

uint32_t random_num32() {
    volatile uint32_t num = *((volatile int *) CV_VP_RANDOM_NUM_BASE);
    return num;
}

extern void __no_irq_handler();

void nested_irq_handler(uint32_t id) {
    // First stack mie, mepc and mstatus
    // Must be done in critical section with MSTATUS.MIE == 0
    volatile uint32_t mie, mepc, mstatus;
    __asm__ volatile("csrr %0, mie" : "=r" (mie));
    __asm__ volatile("csrr %0, mepc" :"=r" (mepc));
    __asm__ volatile("csrr %0, mstatus" : "=r" (mstatus));

    // Re enable interrupts and create window to enable nested irqs
    mstatus_mie_enable();
    for (volatile int i = 0; i < 20; i++);

    // Disable MSTATUS.MIE and restore from critical section
    mstatus_mie_disable();
    __asm__ volatile("csrw mie, %0" : : "r" (mie));
    __asm__ volatile("csrw mepc, %0" : : "r" (mepc));
    __asm__ volatile("csrw mstatus, %0" : : "r" (mstatus));
}

void generic_irq_handler(uint32_t id) {
    __asm__ volatile("csrr %0, mcause": "=r" (mmcause));
    irq_id = id;

    // Increment if interrupt
    if (mmcause >> 31) {
      num_taken_interrupts++;
    }

    if (active_test == 2 || active_test == 3 || active_test == 4) {
        irq_id_q[irq_id_q_ptr++] = id;
    }
    if (active_test == 3) {
        if (nested_irq_valid) {
            nested_irq_valid = 0;
            mm_ram_assert_irq(0x1 << nested_irq, random_num(10,0));
        }
        nested_irq_handler(id);
    }
}

void m_software_irq_handler(void) { generic_irq_handler(SOFTWARE_IRQ_ID); }
void m_timer_irq_handler(void) { generic_irq_handler(TIMER_IRQ_ID); }
void m_external_irq_handler(void) { generic_irq_handler(EXTERNAL_IRQ_ID); }
void m_fast0_irq_handler(void) { generic_irq_handler(FAST0_IRQ_ID); }
void m_fast1_irq_handler(void) { generic_irq_handler(FAST1_IRQ_ID); }
void m_fast2_irq_handler(void) { generic_irq_handler(FAST2_IRQ_ID); }
void m_fast3_irq_handler(void) { generic_irq_handler(FAST3_IRQ_ID); }
void m_fast4_irq_handler(void) { generic_irq_handler(FAST4_IRQ_ID); }
void m_fast5_irq_handler(void) { generic_irq_handler(FAST5_IRQ_ID); }
void m_fast6_irq_handler(void) { generic_irq_handler(FAST6_IRQ_ID); }
void m_fast7_irq_handler(void) { generic_irq_handler(FAST7_IRQ_ID); }
void m_fast8_irq_handler(void) { generic_irq_handler(FAST8_IRQ_ID); }
void m_fast9_irq_handler(void) { generic_irq_handler(FAST9_IRQ_ID); }
void m_fast10_irq_handler(void) { generic_irq_handler(FAST10_IRQ_ID); }
void m_fast11_irq_handler(void) { generic_irq_handler(FAST11_IRQ_ID); }
void m_fast12_irq_handler(void) { generic_irq_handler(FAST12_IRQ_ID); }
void m_fast13_irq_handler(void) { generic_irq_handler(FAST13_IRQ_ID); }
void m_fast14_irq_handler(void) { generic_irq_handler(FAST14_IRQ_ID); }
void m_fast15_irq_handler(void) { generic_irq_handler(FAST15_IRQ_ID); }

// A Special version of the SW Handler (vector 0) used in the direct mode
__attribute__((interrupt ("machine"))) void u_sw_direct_irq_handler(void)  {
    in_direct_handler = 1;
    __asm__ volatile ("csrr %0, mcause" : "=r" (mmcause));
    if (mmcause >> 31) {
      num_taken_interrupts++;
    }
}

__attribute__((naked)) void alt_vector_table_func() {
    __asm__ volatile (
        ".global alt_vector_table\n"
        ".option push\n"
        ".option norvc\n"
        ".align 8\n"
        "alt_vector_table:\n"
        "j u_sw_irq_handler\n"
        "j __no_irq_handler\n"
        "j __no_irq_handler\n"
        "j m_software_irq_handler\n"
        "j __no_irq_handler\n"
        "j __no_irq_handler\n"
        "j __no_irq_handler\n"
        "j m_timer_irq_handler\n"
        "j __no_irq_handler\n"
        "j __no_irq_handler\n"
        "j __no_irq_handler\n"
        "j m_external_irq_handler\n"
        "j __no_irq_handler\n"
        "j __no_irq_handler\n"
        "j __no_irq_handler\n"
        "j __no_irq_handler\n"
        "j m_fast0_irq_handler\n"
        "j m_fast1_irq_handler\n"
        "j m_fast2_irq_handler\n"
        "j m_fast3_irq_handler\n"
        "j m_fast4_irq_handler\n"
        "j m_fast5_irq_handler\n"
        "j m_fast6_irq_handler\n"
        "j m_fast7_irq_handler\n"
        "j m_fast8_irq_handler\n"
        "j m_fast9_irq_handler\n"
        "j m_fast10_irq_handler\n"
        "j m_fast11_irq_handler\n"
        "j m_fast12_irq_handler\n"
        "j m_fast13_irq_handler\n"
        "j m_fast14_irq_handler\n"
        "j m_fast15_irq_handler\n"
        ".option pop\n"
    );
}

__attribute__((naked)) void alt_direct_vector_table_func() {
    __asm__ volatile (
        ".global alt_direct_vector_table\n"
        ".option push\n"
        ".option norvc\n"
        ".align 8\n"
        "alt_direct_vector_table:\n"
        "j u_sw_direct_irq_handler\n"
        ".option pop\n"
    );
}

__attribute__((naked)) void alt_direct_ecall_table_func() {
    __asm__ volatile (
        ".global alt_direct_ecall_table\n"
        ".option push\n"
        ".option norvc\n"
        ".align 8\n"
        "alt_direct_ecall_table:\n"
        "wfi\n"
        "j u_sw_irq_handler\n"
        ".option pop\n"
    );
}

int main(int argc, char *argv[]) {
    volatile int retval;

    num_taken_interrupts   = 0;

    // Enable interrupt performance counter (mhpmcounter3)
    event = EVENT_INTR_TAKEN;
    __asm__ volatile ("csrw 0x323, %0 " :: "r"(event));
    __asm__ volatile ("csrwi 0xB03, 0x0");
    __asm__ volatile ("csrwi 0x320, 0x0");


    retval = memTest();
    if (retval != EXIT_SUCCESS) {
      return retval;
    }

    retval = addTest();
    if (retval != EXIT_SUCCESS) {
      return retval;
    }

    retval = divisionTest();
    if (retval != EXIT_SUCCESS) {
      return retval;
    }

    retval = test2IRQS();
    if (retval != EXIT_SUCCESS) {
      return retval;
    }

    return EXIT_SUCCESS;
    // Clear MIE for final WFI
    mie_disable_all();

    return EXIT_SUCCESS;
}


int divisionTest() {
    uint8_t interrupt = 16;
    
    printf("Division Test \n");

    active_test = 0;

    mstatus_mie_enable();

    //Enable all interrupts
    volatile uint32_t mie = (uint32_t) -1;
    __asm__ volatile("csrw mie, %0" : : "r" (mie));

    uint32_t b = 0x00002;
    uint32_t a = 0xAAAAAAAA;
    uint32_t c;
    uint32_t result;
    int count = 0;


    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (count) : "r" (count));


    //Time interrupt in the middle of the second division instruction
    mm_ram_assert_irq(0x1 << 16, 50);
    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("divu %0, %1, %2\n\t" : "=r" (a) : "r" (a), "r" (b));
    __asm__ volatile("divu %0, %1, %2\n\t" : "=r" (a) : "r" (a), "r" (b));
    __asm__ volatile("divu %0, %1, %2\n\t" : "=r" (a) : "r" (a), "r" (b));

    printf("count %d\n", count);   
    mstatus_mie_disable();

    mie_disable(interrupt);

    return EXIT_SUCCESS;
}

int addTest() {
    uint8_t interrupt = 16;
    
    printf("Revertion Test \n");

    active_test = 0;

    mstatus_mie_enable();

    //Enable all interrupts
    volatile uint32_t mie = (uint32_t) -1;
    __asm__ volatile("csrw mie, %0" : : "r" (mie));

    uint32_t a = 0x12341234;
    uint32_t b = 0x00004567;
    uint32_t c;
    uint32_t result;

    int count = 0;

    mm_ram_assert_irq(0x1 << 16, 4);
    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 2\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 3\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 4\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 5\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 6\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 7\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 8\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 9\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 10\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 11\n\t" : "=r" (count) : "r" (count));

    count++;

    printf("count %d\n", count);

    //mm_ram_assert_irq(0x1 << 16, 3);
    //__asm__ volatile("sw %0, 0(%1)\n\t": : "r" (b), "r" (&c));
    //__asm__ volatile("sw %0, 0(%1)\n\t": : "r" (b), "r" (&c));
    //__asm__ volatile("sw %0, 0(%1)\n\t": : "r" (b), "r" (&c));
    //__asm__ volatile("divu %0, %1, %2\n\t" : "=r" (b) : "r" (b), "r" (b));

    mstatus_mie_disable();

    mie_disable(interrupt);

    return EXIT_SUCCESS;
}

int memTest() {
    
    printf("Memory Test \n");

    active_test = 0;

    mstatus_mie_enable();

    //Enable all interrupts
    volatile uint32_t mie = (uint32_t) -1;
    __asm__ volatile("csrw mie, %0" : : "r" (mie));

    uint32_t a0 = 1; 
    uint32_t a1 = 2; 
    uint32_t a2 = 3;
    uint32_t a3 = 4;
    uint32_t a4 = 5;
    int load_value;
    int count = 0;
    
    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (count) : "r" (count));
    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (count) : "r" (count));



    //Time interrupt in the middle of the load instruction
    mm_ram_assert_irq(0x1 << 16, 8);

    load_value = a0;
    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (load_value) : "r" (load_value));
    a0 = load_value;
    load_value = a1;
    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (load_value) : "r" (load_value));
    a1 = load_value;
    load_value = a2;
    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (load_value) : "r" (load_value));
    a2 = load_value;

    load_value = a3;
    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (load_value) : "r" (load_value));
    a3 = load_value;

    load_value = a4;
    __asm__ volatile("addi %0, %1, 1\n\t" : "=r" (load_value) : "r" (load_value));
    a4 = load_value;

    mstatus_mie_disable();



    return EXIT_SUCCESS;
}

int test2IRQS() {
    printf("TRIGGER 2 IRQS:\n");
    active_test = 2;
    int count = 0;

    // Clear VP irq
    mm_ram_assert_irq(0, 0);

    // Enable all interrupts (MIE and MSTATUS.MIE)
    volatile uint32_t mie = (uint32_t) -1;
    __asm__ volatile("csrw mie, %0" : : "r" (mie));
    mstatus_mie_enable();
    irq_id_q_ptr = 0;

    // Fire 2 IRQs and give time for them to be handled
    mm_ram_assert_irq(0xC0000000, 0);

    count++;
    count++;
    count++;
    count++;
    count++;
    count++;
    count++;
    count++;
    count++;

    printf("count %d\n", count);

    return EXIT_SUCCESS;
}
