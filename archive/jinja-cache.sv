// JINJA CODE

    assign cc_ways_index = 
    %% for i in range(ways_p):
        {ways_size_lp{block_tag_r[i] == cc_pkt_r.addr[31-:tag_size_lp]}} & ways_size_lp'{{i}} || 
    %% endfor
        {ways_size_lp{read_write_miss}} & (open_block_way_index | ({ways_size_lp{set_full}} & evict_block_way_index));

    %% for i in range(ways_p):
    assign block_tag_n[i] = cc_valid_ready? cache_mem_r[set_index][i].tag: block_tag_r[i];
    assign block_state_n[i] = cc_valid_ready? cache_mem_r[set_index][i].block_state: block_state_r[i];
    %% endfor

    // miss if no tags in the proper set match
    assign read_write_miss = 
    %% for i in range(ways_p):
        (block_tag_r[i] != cc_pkt_r.addr[31-:tag_size_lp]) &
    %% endfor
        cc_valid_r;
    
    // set is full if no blocks are invalid
    assign set_full = 
    %% for i in range(ways_p):
        (block_state_r[i] != s_invalid) &
    %% endfor
        1'b1;

    // AND OR tree for finding way index of open block
    // 0 if not exists
    assign open_block_way_index = 
    %% for i in range(ways_p):
        {ways_size_lp{block_state_r[i] == s_invalid}} & ways_size_lp'{{i}} || 
    %% endfor
        '0;
