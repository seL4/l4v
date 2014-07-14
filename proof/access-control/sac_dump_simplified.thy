(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory sac_dump_simplified
imports "../../spec/capDL/Types_D"
begin

text {* the AEP between SAC-C and Timer *}
definition obj0 :: cdl_object where
"obj0 \<equiv> Types_D.Endpoint"

text {* the AEP between RM and Timer *}
definition obj1 :: cdl_object where
"obj1 \<equiv> Types_D.Endpoint"

text {* Timer's asid pool *}
definition obj2 :: cdl_object where
"obj2 \<equiv> Types_D.AsidPool"

text {* RM's asid pool *}
definition obj3 :: cdl_object where
"obj3 \<equiv> Types_D.AsidPool"

text {* SAC-C's asid pool *}
definition obj4 :: cdl_object where
"obj4 \<equiv> Types_D.AsidPool"

text {* SAC-C's CSpace:
Memory: 
 UntypedMem for ranges
           3082_3089, 3118_3122, 3137_3142, 3151_3153, 3155_3193, 
           3258_3372 3410_3505,
 have been collapsed into one  (UntypedMem 3151 undefined).

nic-C's mapped frames

 FrameCap (Standard i) for i=10..42 have been collapsed in 
 FrameCap (Standard 10)
       *}

definition caps5 :: cdl_cap_map where
"caps5 \<equiv> [1 \<mapsto> Types_D.TcbCap (Standard 3079),
                 2 \<mapsto> Types_D.CNodeCap (Standard 6) 0 0,
                 3 \<mapsto> Types_D.PageDirectoryCap (Standard 3063),
                 6 \<mapsto> Types_D.AsidPoolCap (Standard 4),
                 11 \<mapsto> Types_D.UntypedCap (UntypedMem 3151 undefined),
                 283 \<mapsto> Types_D.IrqHandlerCap 27,
                 284 \<mapsto> Types_D.FrameCap (Standard 10) {} 12 True,
                 317 \<mapsto> Types_D.IOSpaceCap (Standard 3057),
                 318 \<mapsto> Types_D.EndpointCap (Standard 9) 0 {Write},
                 319 \<mapsto> Types_D.AsyncEndpointCap (Standard 0) 0 {Read}]"

definition obj5 :: cdl_object where
"obj5 \<equiv> Types_D.CNode \<lparr> cdl_cnode_caps = caps5, cdl_cnode_size_bits = 10 \<rparr>"

definition caps6 :: cdl_cap_map where
"caps6 \<equiv> [0 \<mapsto> Types_D.CNodeCap (Standard 5) 0 0]"

definition obj6 :: cdl_object where
"obj6 \<equiv> Types_D.CNode \<lparr> cdl_cnode_caps = caps6, cdl_cnode_size_bits = 10 \<rparr>"



text {* RM's Cspace 

 UntypedMem for ranges
    3090_3117, 3124_3136, 3143_3150, 3154, 3194_3257, 3373_3409
 have been collapsed into one  (UntypedMem 3124 undefined).
 
 FrameCap (Standard i) for i=43..106 have been collapsed in 
 FrameCap (Standard 43)

 FrameCap (Standard i) for i=107..170 have been collapsed in 
 FrameCap (Standard 107)

 FrameCap (Standard i) for i=171..174 have been collapsed in 
 FrameCap (Standard 171)

*}

definition caps7 :: cdl_cap_map where
"caps7 \<equiv> [1 \<mapsto> Types_D.TcbCap (Standard 3080),
                 2 \<mapsto> Types_D.CNodeCap (Standard 7) 0 0,
                 3 \<mapsto> Types_D.PageDirectoryCap (Standard 3065),
                 6 \<mapsto> Types_D.AsidPoolCap (Standard 3),
                 11 \<mapsto> Types_D.PageDirectoryCap (Standard 3064),
                 12 \<mapsto> Types_D.UntypedCap (UntypedMem 3124 undefined),
                 163 \<mapsto> Types_D.IrqHandlerCap 25,
                 164 \<mapsto> Types_D.FrameCap (Standard 43) {} 12 True,
                 228 \<mapsto> Types_D.IOSpaceCap (Standard 3054),
                 229 \<mapsto> Types_D.IrqHandlerCap 26,
                 230 \<mapsto> Types_D.FrameCap (Standard 107) {} 12 True,
                 294 \<mapsto> Types_D.IOSpaceCap (Standard 3055),
                 295 \<mapsto> Types_D.IrqHandlerCap 28,
                 296 \<mapsto> Types_D.FrameCap (Standard 171) {} 12 True,
                 300 \<mapsto> Types_D.IOSpaceCap (Standard 3056),
                 301 \<mapsto> Types_D.IOPortsCap undefined undefined,
                 302 \<mapsto> Types_D.EndpointCap (Standard 9) 0 {Read},
                 303 \<mapsto> Types_D.AsyncEndpointCap (Standard 1) 0 {Read}]"

definition obj7 :: cdl_object where
"obj7 \<equiv> Types_D.CNode \<lparr> cdl_cnode_caps = caps7, cdl_cnode_size_bits = 10 \<rparr>"


text {* Timer's Cspace *}

definition caps8 :: cdl_cap_map where
"caps8 \<equiv> [1 \<mapsto> Types_D.TcbCap (Standard 3081),
                 2 \<mapsto> Types_D.CNodeCap (Standard 8) 0 0,
                 3 \<mapsto> Types_D.PageDirectoryCap (Standard 3066),
                 6 \<mapsto> Types_D.AsidPoolCap (Standard 2),
                 11 \<mapsto> Types_D.UntypedCap (UntypedMem 3123 undefined),
                 12 \<mapsto> Types_D.IrqHandlerCap 0,
                 13 \<mapsto> Types_D.IOPortsCap undefined undefined,
                 14 \<mapsto> Types_D.AsyncEndpointCap (Standard 0) 4 {Write},
                 15 \<mapsto> Types_D.AsyncEndpointCap (Standard 1) 16 {Write}]"

definition obj8 :: cdl_object where
"obj8 \<equiv> Types_D.CNode \<lparr> cdl_cnode_caps = caps8, cdl_cnode_size_bits = 10 \<rparr>"



text {* endpoint between SAC-C and RM *}
definition obj9 :: cdl_object where
"obj9 \<equiv> Types_D.Endpoint"



text {* nic-C's mapped frames

 FrameCap (Standard i) for i=10..42 have been collapsed in 
 FrameCap (Standard 10)
       *}

definition obj10 :: cdl_object where
"obj10 \<equiv> Types_D.Frame \<lparr> cdl_frame_size_bits = 12 \<rparr>"


text {* Some Nic (say A) mapped frames:

 FrameCap (Standard i) for i=43..106 have been collapsed in 
 FrameCap (Standard 43)
*}

definition obj43 :: cdl_object where
"obj43 \<equiv> Types_D.Frame \<lparr> cdl_frame_size_bits = 12 \<rparr>"


text {* Some Nic (say B) mapped frames:

 FrameCap (Standard i) for i=107..170 have been collapsed in 
 FrameCap (Standard 107)
 
*}


definition obj107 :: cdl_object where
"obj107 \<equiv> Types_D.Frame \<lparr> cdl_frame_size_bits = 12 \<rparr>"


text {* Some Nic (say D) mapped frames:

 FrameCap (Standard i) for i=171..174 have been collapsed in 
 FrameCap (Standard 171)

*}

definition obj171 :: cdl_object where
"obj171 \<equiv> Types_D.Frame \<lparr> cdl_frame_size_bits = 12 \<rparr>"




text {* R's PageTable 1 of 3

 FrameCap (Standard i) for i=175_280, 303_1198, 1449_1454 have been collapsed in 
 FrameCap (Standard 280) {Read}

*}

definition obj280 :: cdl_object where
"obj280 \<equiv> Types_D.Frame \<lparr> cdl_frame_size_bits = 12 \<rparr>"



text {* RM's PageTable 1 of 3

 FrameCap (Standard i) for i=281_287 have been collapsed in 
 FrameCap (Standard 287) {Read}

*}

definition obj287 :: cdl_object where
"obj287 \<equiv> Types_D.Frame \<lparr> cdl_frame_size_bits = 12 \<rparr>"


text {* RM's PageTable 3 of 3 

 FrameCap (Standard i) for i=288, 2994, 2995  have been collapsed in 
 FrameCap (Standard 288) {Read, Write}

*}
definition obj288 :: cdl_object where
"obj288 \<equiv> Types_D.Frame \<lparr> cdl_frame_size_bits = 12 \<rparr>"



text {* Timer's PageTable 1 of 2

 FrameCap (Standard i) for i=289_301 have been collapsed in 
 FrameCap (Standard 301) {Read}

*}

definition obj301 :: cdl_object where
"obj301 \<equiv> Types_D.Frame \<lparr> cdl_frame_size_bits = 12 \<rparr>"



text {* Timer's PageTable 2 of 2

 FrameCap (Standard i) for i=302, 2996, 2997 have been collapsed in 
 FrameCap (Standard 302) {Read, Write}

*}
definition obj302 :: cdl_object where
"obj302 \<equiv> Types_D.Frame \<lparr> cdl_frame_size_bits = 12 \<rparr>"


text {* R's PageTable 2 of 3 

 FrameCap (Standard i) for i=1199_1448,1614_1710  have been collapsed in 
 FrameCap (Standard 1448) {Read}

*}

definition obj1448 :: cdl_object where
"obj1448 \<equiv> Types_D.Frame \<lparr> cdl_frame_size_bits = 12 \<rparr>"



text {* SAC-C's PageTable 1 of 4 

 FrameCap (Standard i) for i=1455_1611, 1711_1966, 2086-2222 have been collapsed in 
 FrameCap (Standard 1455) {Read}

 FrameCap (Standard i) for i=1967_2085, 2332-2478 have been collapsed in 
 FrameCap (Standard 2332) {Read, Write}

*}

definition obj1455 :: cdl_object where
"obj1455 \<equiv> Types_D.Frame \<lparr> cdl_frame_size_bits = 12 \<rparr>"



text {* SAC-C's PageTable 4 of 4 

 FrameCap (Standard i) for i=1612, 2991, 2992  have been collapsed in 
 FrameCap (Standard 1612) {Read, Write}

*}
definition obj1612 :: cdl_object where
"obj1612 \<equiv> Types_D.Frame \<lparr> cdl_frame_size_bits = 12 \<rparr>"



text {* R's PageTable 1 of 3

 FrameCap (Standard i) for i=1613 and 2993 have been collapsed in 
 FrameCap (Standard 1613) {Read}

*}
definition obj1613 :: cdl_object where
"obj1613 \<equiv> Types_D.Frame \<lparr> cdl_frame_size_bits = 12 \<rparr>"



text {* SAC-C's PageTable 2 of 4 

 FrameCap (Standard i) for i=2223_2331, 2479_2990, 2998_3052  have been collapsed in 
 FrameCap (Standard 2223) {Read, Write}

*}

definition obj2223 :: cdl_object where
"obj2223 \<equiv> Types_D.Frame \<lparr> cdl_frame_size_bits = 12 \<rparr>"


text {* SAC-C's PageTable 1 of 4 

 FrameCap (Standard i) for i=1455_1611, 1711_1966, 2086-2222 have been collapsed in 
 FrameCap (Standard 1455) {Read}

 FrameCap (Standard i) for i=1967_2085, 2332-2478 have been collapsed in 
 FrameCap (Standard 2332) {Read, Write}

*}
definition obj2332 :: cdl_object where
"obj2332 \<equiv> Types_D.Frame \<lparr> cdl_frame_size_bits = 12 \<rparr>"


text {* IOPorts and devices *}
definition obj3053 :: cdl_object where
"obj3053 \<equiv> Types_D.TODO (* IOPorts *)"

definition caps3054 :: cdl_cap_map where
"caps3054 \<equiv> empty"

definition obj3054 :: cdl_object where
"obj3054 \<equiv> Types_D.TODO (* IODevice *)"

definition caps3055 :: cdl_cap_map where
"caps3055 \<equiv> empty"

definition obj3055 :: cdl_object where
"obj3055 \<equiv> Types_D.TODO (* IODevice *)"

definition caps3056 :: cdl_cap_map where
"caps3056 \<equiv> empty"

definition obj3056 :: cdl_object where
"obj3056 \<equiv> Types_D.TODO (* IODevice *)"

definition caps3057 :: cdl_cap_map where
"caps3057 \<equiv> empty"

definition obj3057 :: cdl_object where
"obj3057 \<equiv> Types_D.TODO (* IODevice *)"

text {* only keeping only empty cnode 3058 
  (removing 3059_3062 and 35_073756) *}

definition caps3058 :: cdl_cap_map where
"caps3058 \<equiv> empty"

definition obj3058 :: cdl_object where
"obj3058 \<equiv> Types_D.CNode \<lparr> cdl_cnode_caps = caps3058, cdl_cnode_size_bits = 0 \<rparr>"



text {* SAC-C's VSpace (PageDirectory)*}

definition caps3063 :: cdl_cap_map where
"caps3063 \<equiv> [0 \<mapsto> Types_D.PageTableCap (Standard 3072) False,
                    1 \<mapsto> Types_D.PageTableCap (Standard 3071) False,
                    768 \<mapsto> Types_D.PageTableCap (Standard 3070) False,
                    832 \<mapsto> Types_D.PageTableCap (Standard 3067) False]"

definition obj3063 :: cdl_object where
"obj3063 \<equiv> Types_D.PageDirectory \<lparr> cdl_page_directory_caps = caps3063 \<rparr>"


text {* R's VSpace (PageDirectory)*}

definition caps3064 :: cdl_cap_map where
"caps3064 \<equiv> [0 \<mapsto> Types_D.PageTableCap (Standard 3076) False,
                    1 \<mapsto> Types_D.PageTableCap (Standard 3075) False,
                    832 \<mapsto> Types_D.PageTableCap (Standard 3074) False]"

definition obj3064 :: cdl_object where
"obj3064 \<equiv> Types_D.PageDirectory \<lparr> cdl_page_directory_caps = caps3064 \<rparr>"


text {* RM's VSpace (PageDirectory)*}

definition caps3065 :: cdl_cap_map where
"caps3065 \<equiv> [0 \<mapsto> Types_D.PageTableCap (Standard 3077) False,
                    768 \<mapsto> Types_D.PageTableCap (Standard 3073) False,
                    832 \<mapsto> Types_D.PageTableCap (Standard 3068) False]"

definition obj3065 :: cdl_object where
"obj3065 \<equiv> Types_D.PageDirectory \<lparr> cdl_page_directory_caps = caps3065 \<rparr>"



text {* Timer's VSpace (PageDirectory)*}

definition caps3066 :: cdl_cap_map where
"caps3066 \<equiv> [0 \<mapsto> Types_D.PageTableCap (Standard 3078) False,
                    832 \<mapsto> Types_D.PageTableCap (Standard 3069) False]"

definition obj3066 :: cdl_object where
"obj3066 \<equiv> Types_D.PageDirectory \<lparr> cdl_page_directory_caps = caps3066 \<rparr>"


text {* SAC-C's PageTable 4 of 4 

 FrameCap (Standard i) for i=1612, 2991, 2992  have been collapsed in 
 FrameCap (Standard 1612) {Read, Write}

*}
definition caps3067 :: cdl_cap_map where
"caps3067 \<equiv> [0 \<mapsto> Types_D.FrameCap (Standard 1612) {Read, Write} 12 False]"


definition obj3067 :: cdl_object where
"obj3067 \<equiv> Types_D.PageTable \<lparr> cdl_page_table_caps = caps3067 \<rparr>"


text {* RM's PageTable 3 of 3 

 FrameCap (Standard i) for i=288, 2994, 2995  have been collapsed in 
 FrameCap (Standard 288) {Read, Write}

*}
definition caps3068 :: cdl_cap_map where
"caps3068 \<equiv> [0 \<mapsto> Types_D.FrameCap (Standard 288) {Read, Write} 12 False]"

definition obj3068 :: cdl_object where
"obj3068 \<equiv> Types_D.PageTable \<lparr> cdl_page_table_caps = caps3068 \<rparr>"


text {* Timer's PageTable 2 of 2

 FrameCap (Standard i) for i=302, 2996, 2997 have been collapsed in 
 FrameCap (Standard 302) {Read, Write}

*}

definition caps3069 :: cdl_cap_map where
"caps3069 \<equiv> [0 \<mapsto> Types_D.FrameCap (Standard 302) {Read, Write} 12 False]"

definition obj3069 :: cdl_object where
"obj3069 \<equiv> Types_D.PageTable \<lparr> cdl_page_table_caps = caps3069 \<rparr>"

text {* SAC-C's PageTable 3 of 4 

 FrameCap (Standard i) for i=10_42  have been collapsed in 
 FrameCap (Standard 10) {Read, Write}

*}

definition caps3070 :: cdl_cap_map where
"caps3070 \<equiv> [384 \<mapsto> Types_D.FrameCap (Standard 10) {Read, Write} 12 False]"

definition obj3070 :: cdl_object where
"obj3070 \<equiv> Types_D.PageTable \<lparr> cdl_page_table_caps = caps3070 \<rparr>"



text {* SAC-C's PageTable 2 of 4 

 FrameCap (Standard i) for i=2223_2331, 2479_2990, 2998_3052  have been collapsed in 
 FrameCap (Standard 2223) {Read, Write}

*}

definition caps3071 :: cdl_cap_map where
"caps3071 \<equiv> [0 \<mapsto> Types_D.FrameCap (Standard 2223) {Read, Write} 12 False]"

definition obj3071 :: cdl_object where
"obj3071 \<equiv> Types_D.PageTable \<lparr> cdl_page_table_caps = caps3071 \<rparr>"


text {* SAC-C's PageTable 1 of 4 

 FrameCap (Standard i) for i=1455_1611, 1711_1967, 2086-2222 have been collapsed in 
 FrameCap (Standard 1455) {Read}

 FrameCap (Standard i) for i=1967_2085, 2332-2478 have been collapsed in 
 FrameCap (Standard 2332) {Read, Write}

*}

definition caps3072 :: cdl_cap_map where
"caps3072 \<equiv> [208 \<mapsto> Types_D.FrameCap (Standard 1455) {Read} 12 False,
                    877 \<mapsto> Types_D.FrameCap (Standard 2332) {Read, Write} 12 False]"

definition obj3072 :: cdl_object where
"obj3072 \<equiv> Types_D.PageTable \<lparr> cdl_page_table_caps = caps3072 \<rparr>"


text {* RM's PageTable 2 of 3 (mapped frames for Nic A, B, D)

 FrameCap (Standard i) for i=43..106 have been collapsed in 
 FrameCap (Standard 43)

 FrameCap (Standard i) for i=107..170 have been collapsed in 
 FrameCap (Standard 107)

 FrameCap (Standard i) for i=171..174 have been collapsed in 
 FrameCap (Standard 171)
 *}


definition caps3073 :: cdl_cap_map where
"caps3073 \<equiv> [512 \<mapsto> Types_D.FrameCap (Standard 43) {Read, Write} 12 False,
                    576 \<mapsto> Types_D.FrameCap (Standard 107) {Read, Write} 12 False,
                    768 \<mapsto> Types_D.FrameCap (Standard 171) {Read, Write} 12 False]"

definition obj3073 :: cdl_object where
"obj3073 \<equiv> Types_D.PageTable \<lparr> cdl_page_table_caps = caps3073 \<rparr>"


text {* R's PageTable 1 of 3

 FrameCap (Standard i) for i=1613 and 2993 have been collapsed in 
 FrameCap (Standard 1613) {Read}

*}

definition caps3074 :: cdl_cap_map where
"caps3074 \<equiv> [0 \<mapsto> Types_D.FrameCap (Standard 1613) {Read} 12 False,
                    1 \<mapsto> Types_D.FrameCap (Standard 2993) {Read} 12 False]"

definition obj3074 :: cdl_object where
"obj3074 \<equiv> Types_D.PageTable \<lparr> cdl_page_table_caps = caps3074 \<rparr>"


text {* R's PageTable 2 of 3

 FrameCap (Standard i) for i=1199_1448,1614_1710  have been collapsed in 
 FrameCap (Standard 1448) {Read}

*}
definition caps3075 :: cdl_cap_map where
"caps3075 \<equiv> [0 \<mapsto> Types_D.FrameCap (Standard 1448) {Read} 12 False]"

definition obj3075 :: cdl_object where
"obj3075 \<equiv> Types_D.PageTable \<lparr> cdl_page_table_caps = caps3075 \<rparr>"


text {* R's PageTable 1 of 3

 FrameCap (Standard i) for i=175_280, 303_1198, 1449_1454 have been collapsed in 
 FrameCap (Standard 280) {Read}

*}

definition caps3076 :: cdl_cap_map where
"caps3076 \<equiv> [16 \<mapsto> Types_D.FrameCap (Standard 280) {Read} 12 False]"

definition obj3076 :: cdl_object where
"obj3076 \<equiv> Types_D.PageTable \<lparr> cdl_page_table_caps = caps3076 \<rparr>"


text {* RM's PageTable 1 of 3

 FrameCap (Standard i) for i=281_287 have been collapsed in 
 FrameCap (Standard 287) {Read}

*}

definition caps3077 :: cdl_cap_map where
"caps3077 \<equiv> [16 \<mapsto> Types_D.FrameCap (Standard 287) {Read} 12 False]"

definition obj3077 :: cdl_object where
"obj3077 \<equiv> Types_D.PageTable \<lparr> cdl_page_table_caps = caps3077 \<rparr>"

text {* Timer's PageTable 1 of 2

 FrameCap (Standard i) for i=289_301 have been collapsed in 
 FrameCap (Standard 301) {Read}

*}

definition caps3078 :: cdl_cap_map where
"caps3078 \<equiv> [16 \<mapsto> Types_D.FrameCap (Standard 301) {Read} 12 False]"

definition obj3078 :: cdl_object where
"obj3078 \<equiv> Types_D.PageTable \<lparr> cdl_page_table_caps = caps3078 \<rparr>"


text {* SAC-C's tcb *}

definition caps3079 :: cdl_cap_map where
"caps3079 \<equiv> [0 \<mapsto> Types_D.CNodeCap (Standard 6) 0 0,
                    1 \<mapsto> Types_D.PageDirectoryCap (Standard 3063),
                    2 \<mapsto> Types_D.ReplyCap (Standard 3079),
                    4 \<mapsto> Types_D.FrameCap (Standard 1612) {} 12 True]"

definition obj3079 :: cdl_object where
"obj3079 \<equiv> Types_D.Tcb \<lparr> cdl_tcb_caps = caps3079, cdl_tcb_fault_endpoint = undefined, cdl_tcb_intent = undefined \<rparr>"


text {*RM's tcb *}
definition caps3080 :: cdl_cap_map where
"caps3080 \<equiv> [0 \<mapsto> Types_D.CNodeCap (Standard 7) 0 0,
                    1 \<mapsto> Types_D.PageDirectoryCap (Standard 3065),
                    2 \<mapsto> Types_D.ReplyCap (Standard 3080),
                    4 \<mapsto> Types_D.FrameCap (Standard 288) {} 12 True]"

definition obj3080 :: cdl_object where
"obj3080 \<equiv> Types_D.Tcb \<lparr> cdl_tcb_caps = caps3080, cdl_tcb_fault_endpoint = undefined, cdl_tcb_intent = undefined \<rparr>"


text {* Timer's tcb *}

definition caps3081 :: cdl_cap_map where
"caps3081 \<equiv> [0 \<mapsto> Types_D.CNodeCap (Standard 8) 0 0,
                    1 \<mapsto> Types_D.PageDirectoryCap (Standard 3066),
                    2 \<mapsto> Types_D.ReplyCap (Standard 3081),
                    4 \<mapsto> Types_D.FrameCap (Standard 302) {} 12 True]"

definition obj3081 :: cdl_object where
"obj3081 \<equiv> Types_D.Tcb \<lparr> cdl_tcb_caps = caps3081, cdl_tcb_fault_endpoint = undefined, cdl_tcb_intent = undefined \<rparr>"


text {* one untyped for the Timer *}

definition obj3123 :: cdl_object where
"obj3123 \<equiv> Types_D.Untyped"


text {* RM's Memory

 UntypedMem for ranges
    3090_3117, 3124_3136, 3143_3150, 3154, 3194_3257, 3373_3409
 have been collapsed into one  (UntypedMem 3124 undefined).
 
*}

definition obj3124 :: cdl_object where
"obj3124 \<equiv> Types_D.Untyped"
 

text {* SAC-C's memory

 UntypedMem for ranges
           3082_3089, 3118_3122, 3137_3142, 3151_3153, 3155_3193, 
           3258_3372 3410_3505,
 have been collapsed into one  (UntypedMem 3151 undefined) *}

definition obj3151 :: cdl_object where
"obj3151 \<equiv> Types_D.Untyped"  





definition objects :: "cdl_object_id \<Rightarrow> cdl_object option" where
"objects \<equiv> [(Standard 0) \<mapsto> obj0,
                   (Standard 1) \<mapsto> obj1, (Standard 2) \<mapsto> obj2,
                   (Standard 3) \<mapsto> obj3, (Standard 4) \<mapsto> obj4,
                   (Standard 5) \<mapsto> obj5, (Standard 6) \<mapsto> obj6,
                   (Standard 7) \<mapsto> obj7, (Standard 8) \<mapsto> obj8,
                   (Standard 9) \<mapsto> obj9, (Standard 10) \<mapsto> obj10,
                   (Standard 43) \<mapsto> obj43, 
                   (Standard 107) \<mapsto> obj107, 
                   (Standard 171) \<mapsto> obj171, 
                   (Standard 280) \<mapsto> obj280, 
                   (Standard 287) \<mapsto> obj287,
                   (Standard 288) \<mapsto> obj288,
                   (Standard 301) \<mapsto> obj301,
                   (Standard 302) \<mapsto> obj302,
                   (Standard 1448) \<mapsto> obj1448,
                   (Standard 1455) \<mapsto> obj1455,
                   (Standard 1612) \<mapsto> obj1612,
                   (Standard 1613) \<mapsto> obj1613,
                   (Standard 2223) \<mapsto> obj2223,
                   (Standard 2332) \<mapsto> obj2332,
                   (Standard 3053) \<mapsto> obj3053,
                   (Standard 3054) \<mapsto> obj3054,
                   (Standard 3055) \<mapsto> obj3055,
                   (Standard 3056) \<mapsto> obj3056,
                   (Standard 3057) \<mapsto> obj3057,
                   (Standard 3058) \<mapsto> obj3058,
                   (Standard 3063) \<mapsto> obj3063,
                   (Standard 3064) \<mapsto> obj3064,
                   (Standard 3065) \<mapsto> obj3065,
                   (Standard 3066) \<mapsto> obj3066,
                   (Standard 3067) \<mapsto> obj3067,
                   (Standard 3068) \<mapsto> obj3068,
                   (Standard 3069) \<mapsto> obj3069,
                   (Standard 3070) \<mapsto> obj3070,
                   (Standard 3071) \<mapsto> obj3071,
                   (Standard 3072) \<mapsto> obj3072,
                   (Standard 3073) \<mapsto> obj3073,
                   (Standard 3074) \<mapsto> obj3074,
                   (Standard 3075) \<mapsto> obj3075,
                   (Standard 3076) \<mapsto> obj3076,
                   (Standard 3077) \<mapsto> obj3077,
                   (Standard 3078) \<mapsto> obj3078,
                   (Standard 3079) \<mapsto> obj3079,
                   (Standard 3080) \<mapsto> obj3080,
                   (Standard 3081) \<mapsto> obj3081,
                   (UntypedMem 3123 undefined) \<mapsto> obj3123,
                   (UntypedMem 3124 undefined) \<mapsto> obj3124,
                   (UntypedMem 3151 undefined) \<mapsto> obj3151]" 
                

definition irqs :: "cdl_irq \<Rightarrow> cdl_object_id" where
"irqs \<equiv> undefined (0 := Standard 3058)"

definition state :: cdl_state where
"state \<equiv> \<lparr> cdl_arch = IA32, cdl_objects = objects, cdl_cdt = undefined, cdl_current_thread = undefined, cdl_irq_node = irqs, cdl_untyped_covers = undefined \<rparr>"

end
