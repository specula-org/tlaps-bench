------------------------------- MODULE typedefs --------------------------------
EXTENDS Variants

typedefs_aliases == TRUE

S1 == "S1_OF_STEP"
S2 == "S2_OF_STEP"
S3 == "S3_OF_STEP"

M1(src, round, value) == [ src |-> src, r |-> round, v |-> value ]

Q2(src, round) == Variant("Q", [ src |-> src, r |-> round ])

IsQ2(msg) == VariantTag(msg) = "Q"

AsQ2(msg) == VariantGetUnsafe("Q", msg)

D2(src, round, value) == Variant("D", [ src |-> src, r |-> round, v |-> value ])

IsD2(msg) == VariantTag(msg) = "D"

AsD2(msg) == VariantGetUnsafe("D", msg)

================================================================================
