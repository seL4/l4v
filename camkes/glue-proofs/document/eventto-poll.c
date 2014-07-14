int EventTo_poll(void) {
    seL4_Word *badge = get_badge();
    seL4_Poll(6, badge);
    return *badge == PENDING;
}
