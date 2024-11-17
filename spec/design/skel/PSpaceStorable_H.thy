(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory PSpaceStorable_H
imports
  Structures_H
  KernelStateData_H
  "Lib.DataMap"
begin

arch_requalify_types (H)
  arch_kernel_object_type

arch_requalify_consts (H)
  archTypeOf

lemma UserData_singleton [simp]:
  "(v = UserData) = True" "(UserData = v) = True"
  by (cases v, simp)+

lemma UserDataDevice_singleton [simp]:
  "(v = UserDataDevice) = True" "(UserDataDevice = v) = True"
  by (cases v, simp)+

datatype
  kernel_object_type =
    EndpointT
  | NotificationT
  | CTET
  | TCBT
  | SchedContextT
  | ReplyT
  | UserDataT
  | UserDataDeviceT
  | KernelDataT
  | ArchT arch_kernel_object_type

primrec
  koTypeOf :: "kernel_object \<Rightarrow> kernel_object_type"
where
  "koTypeOf (KOEndpoint e) = EndpointT"
| "koTypeOf (KONotification e) = NotificationT"
| "koTypeOf (KOCTE e) = CTET"
| "koTypeOf (KOTCB e) = TCBT"
| "koTypeOf (KOSchedContext e) = SchedContextT"
| "koTypeOf (KOReply e) = ReplyT"
| "koTypeOf (KOUserData) = UserDataT"
| "koTypeOf (KOUserDataDevice) = UserDataDeviceT"
| "koTypeOf (KOKernelData) = KernelDataT"
| "koTypeOf (KOArch e) = ArchT (archTypeOf e)"

definition
  read_typeError :: "unit list \<Rightarrow> kernel_object \<Rightarrow> 'a kernel_r" where
  "read_typeError t1 t2 \<equiv> ofail"

definition
  typeError :: "unit list \<Rightarrow> kernel_object \<Rightarrow> 'a kernel" where
  "typeError t1 t2 \<equiv> fail"

definition
  read_alignError :: "nat \<Rightarrow> 'a kernel_r" where
  "read_alignError n \<equiv> ofail"

definition
  alignError :: "nat \<Rightarrow> 'a kernel" where
  "alignError n \<equiv> fail"

definition
  read_alignCheck :: "machine_word \<Rightarrow> nat \<Rightarrow> unit kernel_r" where
  "read_alignCheck x n \<equiv> ounless ((x && mask n) = 0) $ read_alignError n"

definition
  alignCheck :: "machine_word \<Rightarrow> nat \<Rightarrow> unit kernel" where
  "alignCheck x n \<equiv> gets_the $ read_alignCheck x n"


definition
  read_magnitudeCheck :: "machine_word \<Rightarrow> machine_word option \<Rightarrow> nat \<Rightarrow> unit kernel_r"
where
 "read_magnitudeCheck x y n \<equiv>
    case y of None \<Rightarrow> oreturn ()
            | Some z \<Rightarrow> oassert (\<not> (z - x < 1 << n))"

definition
  magnitudeCheck :: "machine_word \<Rightarrow> machine_word option \<Rightarrow> nat \<Rightarrow> unit kernel"
where
 "magnitudeCheck x y n \<equiv> gets_the $ read_magnitudeCheck x y n"


class pre_storable =
  fixes injectKO :: "'a \<Rightarrow> kernel_object"
  fixes projectKO_opt :: "kernel_object \<Rightarrow> 'a option"
  fixes koType :: "'a itself \<Rightarrow> kernel_object_type"

  assumes project_inject: "(projectKO_opt ko = Some v) = (injectKO v = ko)"
  assumes project_koType: "(\<exists>v. projectKO_opt ko = Some (v::'a)) = (koTypeOf ko = koType TYPE('a))"
begin

definition projectKO :: "kernel_object \<Rightarrow> 'a kernel_r" where
  "projectKO e \<equiv> oassert_opt (projectKO_opt e)"

definition objBits :: "'a \<Rightarrow> nat" where
  "objBits v \<equiv> objBitsKO (injectKO v)"

definition loadObject_default ::
  "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word option \<Rightarrow> kernel_object \<Rightarrow> 'a kernel_r" where
  "loadObject_default ptr ptr' next obj \<equiv> do {
     oassert (ptr = ptr');
     val \<leftarrow> projectKO obj;
     oassert (is_aligned ptr (objBits val));
     oassert (objBits val < word_bits);
     read_magnitudeCheck ptr next (objBits val);
     oreturn val
  }"

definition updateObject_default ::
  "'a \<Rightarrow> kernel_object \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word option \<Rightarrow> kernel_object kernel"
  where
  "updateObject_default val oldObj ptr ptr' next \<equiv> do
     assert (ptr = ptr');
     (_ :: 'a) \<leftarrow> gets_the $ projectKO oldObj;
     assert (objBitsKO (injectKO val) = objBitsKO oldObj);
     alignCheck ptr (objBits val);
     assert (objBits val < word_bits);
     magnitudeCheck ptr next (objBits val);
     return (injectKO val)
  od"

end

class pspace_storable = pre_storable +
  fixes makeObject :: 'a

  \<comment>\<open>
    `loadObject` is only used in the generic definition of `getObject`. It
    describes how to extract a value of type `'a` from memory.

    If `(obj, _) \<in> loadObjext p before after ko` within `getObject`, then:
      - @{term "p :: machine_word"} is the addres that we want to read an
        instance of `'a` from.
      - @{term "before :: machine_word"} is the address of the nearest
        object at or before `p`.
      - @{term "after :: machine_word option"} is the address of the nearest
        object after `p`, if any (for checking overlap).
      - @{term "ko :: kernel_object"} is the object currently at `before`.
      - @{term "obj :: 'a"} is the value extracted from `ko`.

    Graphically, the "memory" looks like this:

    before  p              after
    |-------|--+-----+-----|---|
    |       +~~+ <---+---------- The span of obj, the object we want to extract.
    +~~~~~~~~~~~~~~~~+ <-------- The span of ko, the existing object that spans obj.

                           +~~~+ The span of whatever object comes after obj.
                                 We don't care about this beyond making sure
                                 it doesn't overlap with ko.

    In almost every case, the object in memory (ko) is the same type of object
    as the one being loaded (obj). For example, for a reply object our parameters
    look like this:

    p, before
    |-----------|
    +~~~~~~~~~~~+ <- The span of two objects:
                     - ko, the existing object (which should be a reply object).
                     - obj, the object that we want to load from memory. This will
                       just be ko projected through @{term projectKO}.

    In these simple cases, @{term loadObject_default} is a good specification
    for how to load an instance of `'a` from memory.

    The only interesting case is when we're loading a CTE, which might be
    inside a TCB. Then memory looks like this:

    before  p
    |-------|--+-----+
    |       +~~+ <---+---- The span of obj, i.e. the CTE which we're reading from
    |                |     memory.
    +~~~~~~~~~~~~~~~~+ <-- The span of ko, i.e. the TCB surrounding and containing
                           obj.

    In this case, the process for extracting the CTE from the surrounding TCB
    is more involved. See `loadObject_cte` in `ObjectInstances_H`.
  \<close>
  fixes loadObject :: "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word option \<Rightarrow> kernel_object \<Rightarrow> 'a kernel_r"

  \<comment>\<open>
    `updateObject` is only used in the generic definition of `setObject`,
    but it shows up in a few lemma statements as well. It describes how to update
    the kernel object contents of memory depending on what's already in that
    memory.

    If `(ko', _) \<in> updateObject v ko p before after s` within `setObject`, then:
      - @{term "v :: 'a"} is the new object you want to write at pointer
        @{term "p :: machine_word"}.
      - @{term "before :: machine_word"} is the address of the nearest
        object at or before `p`.
      - @{term "ko :: kernel_object"} is the object currently at `before`.
      - @{term "after :: machine_word option"} should be the address of the nearest
        object after `p`, if any (for checking overlap).
      - The returned value @{term "ko' :: kernel_object"} is the old object `ko`,
        updated as required by `v`. This value gets inserted by `setObject` into
        memory at the address `before`.

    Graphically, the "memory" looks like this:

    before  p              after
    |-------|--+-----+-----|---|
    |       +~~+ <---+---------- The span of v, the object we want to insert.
    +~~~~~~~~~~~~~~~~+ <-------- The span of ko, the existing object that spans v.
                                 This is also the span of ko', which will be what
                                 gets put into memory after the update.

                           +~~~+ The span of whatever object comes after ko.
                                 We don't care about this beyond making sure
                                 it doesn't overlap with ko before or after it
                                 gets updated with v.

    In almost every case, the object in memory (ko) is the same type of object
    as the one being inserted (v). For example, for a reply object our parameters
    look like this:

    p, before
    |-----------|
    +~~~~~~~~~~~+ <- The span of three objects:
                     - v, the new reply object we want to insert.
                     - ko, the existing object (which should be a reply object).
                     - ko', the new object (which should be a reply object if
                       the previous one was).

    In these simple cases, @{term updateObject_default} is a good specification
    for how to update the existing kernel object.

    The only interesting case is when we're updating a CTE, which might be
    inside a TCB. Then memory looks like this:

    before  p
    |-------|--+-----+
    |       +~~+ <---+---- The span of v, i.e. the CTE which we're inserting into
    |                |     memory.
    +~~~~~~~~~~~~~~~~+ <-- The span of ko, i.e. the TCB surrounding and containing v.
                           This is also the span of ko', which is "just" a copy
                           of ko with the relevant CTE updated.

    In this case, the process for updating the surrounding TCB is more involved.
    See `updateObject_cte` in `ObjectInstances_H`.
  \<close>
  fixes updateObject :: "'a \<Rightarrow> kernel_object \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow>
                              machine_word option \<Rightarrow> kernel_object kernel"

  \<comment>\<open>
    If updating an object succeeds, then the type of the updated object (ko')
    should be the same as the original object (ko).
  \<close>
  assumes updateObject_type:
  "(ko', s') \<in> fst (updateObject v ko p p' p'' s) \<Longrightarrow> koTypeOf ko' = koTypeOf ko"
  assumes updateObject_size:
  "(ko', s') \<in> fst (updateObject v ko p p' p'' s) \<Longrightarrow> objBitsKO ko' = objBitsKO ko"

end
