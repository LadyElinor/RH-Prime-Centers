// Signed and unsigned losses on the finite grid of endpoints and doubled primes.
// Bounds are for 2*F, in fixed-point units 2^-80, as in verify.cpp.
struct CheckpointLoss {
    Pos left, right;
    size_t count = 0;
    Bounds start{}, lowest{}, increment{}, downward{};
    Pos minimum_x = 0;
    Pos first_possible_excess = 0, first_definite_excess = 0;
    std::vector<Pos> splits;
    Pos previous_x = 0;
    Bounds previous_value{}, block_start{}, block_downward{};
    I runner_lower = I(1) << 124;

    void record(Pos x, Bounds absolute) {
        ++count;
        if (x == left) {
            start = block_start = absolute;
        } else {
            // If increment belongs to [lo,hi], its negative part belongs to
            // [max(0,-hi),max(0,-lo)]. No assumption on its sign is needed.
            Bounds drop{std::max(I(0), -increment.hi), std::max(I(0), -increment.lo)};
            downward.lo += drop.lo;
            downward.hi += drop.hi;
            block_downward.lo += drop.lo;
            block_downward.hi += drop.hi;
            if (block_downward.hi >= block_start.lo) {
                require(block_downward.lo > block_start.hi, "greedy split ambiguous");
                splits.push_back(previous_x);
                block_start = previous_value;
                block_downward = drop;
                require(block_downward.hi < block_start.lo, "single edge exhausts its budget");
            }
        }
        if (!first_possible_excess && downward.hi >= start.lo) first_possible_excess = x;
        if (!first_definite_excess && downward.lo > start.hi) first_definite_excess = x;
        previous_x = x;
        previous_value = absolute;
        increment = {};
        if (minimum_x == 0 || absolute.lo < lowest.lo) {
            if (minimum_x != 0) runner_lower = lowest.lo;
            minimum_x = x;
            lowest = absolute;
        } else {
            runner_lower = std::min(runner_lower, absolute.lo);
        }
    }
};

void certify_checkpoint_losses(Word log2, const std::vector<Pos>& primes,
                               const std::vector<Word>& logs) {
    // The published six intervals, then nested doublings with a common start.
    std::vector<CheckpointLoss> windows{{400,800},{256,1024},{20736,248832},
        {331776,7962624},{8503056,xmax},{256,xmax}};
    constexpr Pos base = 8503056;
    for (Pos multiplier : {2,4,8,16,32}) windows.push_back({base,base*multiplier});
    std::vector<Pos> edges;
    for (const auto& w : windows) {
        edges.push_back(w.left);
        edges.push_back(w.right);
    }
    visit_pieces(edges,log2,primes,logs,[&](Pos prev, Pos x, bool center, const Line& line) {
        Bounds change{line.slope.lo*(x-prev), line.slope.hi*(x-prev)};
        Bounds absolute = value(line,x);
        for (auto& w : windows) {
            if (x < w.left || x > w.right) continue;
            if (prev >= w.left) {
                w.increment.lo += change.lo;
                w.increment.hi += change.hi;
            }
            if (center || x == w.left || x == w.right) w.record(x,absolute);
        }
    });

    std::cout << "left,right,checkpoints,minimum_x,start_lo,start_hi,"
                 "loss_lo,loss_hi,downward_lo,downward_hi,first_excess_x,blocks,interior_splits\n";
    for (const auto& w : windows) {
        require(w.count >= 2 && w.lowest.hi < w.runner_lower, "minimum unresolved");
        Bounds loss{};
        if (w.minimum_x != w.left)
            loss = {w.start.lo-w.lowest.hi, w.start.hi-w.lowest.lo};
        require(loss.lo >= 0 && loss.lo <= w.downward.hi, "loss bounds inconsistent");
        require(w.first_possible_excess == w.first_definite_excess,
                "first excess not separated by interval arithmetic");
        std::cout << w.left << ',' << w.right << ',' << w.count << ',' << w.minimum_x;
        for (I bound : {w.start.lo,w.start.hi,loss.lo,loss.hi,w.downward.lo,w.downward.hi})
            std::cout << ',' << integer_text(bound);
        std::cout << ',' << w.first_definite_excess << ',' << (w.splits.size()+1) << ',';
        for (size_t i=0; i<w.splits.size(); ++i) {
            if (i) std::cout << '|';
            std::cout << w.splits[i];
        }
        std::cout << '\n';
    }
}
