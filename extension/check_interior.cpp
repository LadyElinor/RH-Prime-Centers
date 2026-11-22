// A positive affine numerator can hide a normalized minimum between endpoints.
#define main prime_certificate_main
#include "verify.cpp"
#undef main

int main() {
    const Line line{{scale,scale},{4*scale,4*scale}};
    // (x+4)/sqrt(x) has endpoint values 5 and 13/3 on [1,9]
    // and a unique interior minimum of 4 at x=4.
    for(int tenths : {39,41}) {
        Window control(1,9,16,Word(tenths)*1000000);
        I synthetic_upper=4*scale*tenths/10; // At x=16, sqrt(x)=4.
        mpz_class upper=big(synthetic_upper);
        control.witness_upper_sq=upper*upper;
        bool caught_interior=false;
        try {
            control.normalized_piece(1,9,line,value(line,1),value(line,9),sqrt_ceiling(9));
        } catch (const std::exception& e) {
            if (std::string(e.what()) != "interior stationary point overlaps the witness") throw;
            caught_interior=true;
        }
        require(caught_interior==(tenths==41) && control.exact_comparisons==1,
                "normalized interior control failed");
    }
}
