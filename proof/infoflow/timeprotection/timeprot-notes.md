# Design Decisions

## Single addresses in TA vs both virtual and physical
`touched_addresses` in ASpec is just `machine_word set`, which is only recording (kernel?) virtual addresses. Our time protection locale requires its `touched_addresses` to be pairs of virtual and physical addresses. We are sure (Scott is sure) we don't want to introduce translation via page tables into the TP locale, so our options are:
- (1) Perform V->A translation at the time we touch addresses in the ASpec. This requires a page table lookup, but we are confident that it will only be via the kernel mappings, which means the translation is subtraction of a constant.
- (2) Map the virtual-only `touched_addresses` set into a virtual-and-physical set during the locale instantiation.
	- This option is a lot easier to implement, and our assumption is correct that we would have always performed the same subtraction anyway.
	- This can be assisted by only performing a mapping when the address is in kernel virtual space.
	- We still need to make sure that the `touched_addresses` mappings are different for user steps. This will probably be ok in the instantiation.

## NLDS (next latest domain-switch start)
The TP locale requires a `time => time` function we call `nlds` that, given the current wall-clock time, will return the wall-clock time that the next domain-switch will definitely have started by.

Why is it 'latest'? Because there is the wall-clock time that the timer interrupt is scheduled to arrive, and there is the *actual* time where the kernel will handle this interrupt, and there is a potential delay between these two. This means that domain-switches don't always start *exactly* on schedule, so we need to account for that. The locale itself really does want to think about the *latest* domainswitch start time.

Why do we expose this 'latest' complication to the locale implementer? Maybe we don't need to. We could make a variation that asks for `next_domainswitch_start`, and `WC_timerirq_delay` and computes NLDS from that. This wouldn't be too hard.

### Definitions that reply on NLDS
- `uwr_notrunning` requires `nlds (tm s1) = nlds (tm s2)`
- We sometimes assert `time_bounded_traces` saying that no trace will go past `nlds (tm s)`
	- I think this is totally sensible.
- `gadget_trace` will pad out to `nlds (tm s)`

### Properties that must hold of `nlds`
- `next_latest_domainswitch_start_in_future` :: `nlds t >= t`
- `next_latest_domainswitch_start_flatsteps` :: [`nlds` is a step function with inside corners on x=y]

### How we currently define NLDS
- In `det_ext` there is `domain_list_internal` which specifies the sequence of domains to execute and how many ticks we get. We ask for `time_per_tick`, and multiply tick counts by this to get a modified list. This is passed to a `schedule_oracle` interpretation with an appropriate `timer_delay_max`, which creates NLDS function and proofs of the required lemmas above.
