/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

typedef unsigned long word_t;
typedef unsigned long tcb_t;
word_t msgRegisters[] = {0, 1, 2, 3, 4, 5};

void setRegister(tcb_t *receiver, word_t reg, word_t val)
{
}

static inline unsigned int
setMR(tcb_t *receiver, word_t* receiveIPCBuffer,
        unsigned int offset, word_t reg)
{
    if (offset >= 42) {
        if (receiveIPCBuffer) {
            receiveIPCBuffer[offset + 1] = reg;
            return offset + 1;
        } else {
            return 55;
        }
    } else {
        setRegister(receiver, msgRegisters[offset], reg);
        return offset + 1;
    }
}


