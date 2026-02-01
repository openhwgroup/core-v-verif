'''
Created on Jul 23, 2021

@author: mballance
'''


class WildcardBinFactory(object):
    
    @classmethod
    def str2bin(cls, val) -> tuple:
        # val is string in oct, hex, or bin

        value = 0
        mask = 0
        
        if val.startswith("0o") or val.startswith("0O"):
            # octal format
            for c in val[2:]:
                if c != '_':
                    value <<= 3
                    mask <<= 3
                    if c not in ['x', 'X', '?']:
                        mask |= 0x7
                        value |= int(c, 8)
        elif val.startswith("0x") or val.startswith("0X"):
            for c in val[2:]:
                if c != '_':
                    value <<= 4
                    mask <<= 4
                    if c not in ['x', 'X', '?']:
                        mask |= 0xF
                        value |= int(c, 16)
        elif val.startswith("0b") or val.startswith("0B"):
            for c in val[2:]:
                if c != '_':
                    value <<= 1
                    mask <<= 1
                    if c not in ['x', 'X', '?']:
                        mask |= 0x1
                        value |= int(c, 2)
        else:
            raise Exception("unknown base for value %s" % str(val))
        
        return (value,mask)
    
    @classmethod
    def valmask2binlist(cls, value, mask):
        """Converts value/mask representation to a list of bin specifications"""
        
        n_bits = 0
        
        mask_t = mask
        bit_i = 0

        total_mask_bits = 0
        directives = []
        while mask_t != 0:
            if (mask_t & 1) == 0:
                # Collect this grouping
                group_start_bit = bit_i
                group_n_bits = 0
                while (mask_t & 1) == 0:
                    group_n_bits += 1
                    total_mask_bits += 1
                    mask_t >>= 1
                    bit_i += 1
                    pass
                directives.append((group_start_bit, group_n_bits))
            else:
                mask_t >>= 1
                bit_i += 1
                
        if total_mask_bits > 20:
            raise Exception("Wildcard array bins limited to 20 mask bits")
        
        ranges = []
        for val in range(0, (1 << total_mask_bits)):

            val_i = val
            val_t = (value & mask)
            for d in directives:
                val_t |= ((val_i & ((1 << d[1])-1)) << d[0])
                val_i >>= d[1]
                
            if len(ranges) > 0 and ranges[-1][1]+1 == val_t:
                ranges[-1] = (ranges[-1][0], val_t)
            else:  
                ranges.append((val_t, val_t))

        return ranges

