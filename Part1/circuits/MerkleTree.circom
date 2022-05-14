pragma circom 2.0.0;

include "../node_modules/circomlib/circuits/poseidon.circom";

template HashMath(z) {
    signal input oldHash[2**z];
    signal output newHash[2**(z-1)];
    
    component poseidonI[2**(z-1)];
    
    for (var i = 0; i < 2**(z-1); i++) {
        poseidonI[i] = Poseidon(2);
        poseidonI[i].inputs[0] <== oldHash[2*i];
        poseidonI[i].inputs[1] <== oldHash[2*i+1];
        newHash[i] <== poseidonI[i].out;
    }
}

template CheckRoot(n) { // compute the root of a MerkleTree of n Levels 
    signal input leaves[2**n];
    signal output root;

    //[assignment] insert your code here to calculate the Merkle root from 2^n leaves
    signal simp[2**(n+1)-1];

    component solvent[n-1];

    for (var i = 0; i < 2**n; i++) {
        solvent[i] <== leaves[i];
    }

    var izx = 0;
    
    for (var z = n; z > 0; z--) {
        solvent[n-z] = HashMath(z);
        for (var i = 0; i < 2**z; i++) {
            solvent[n-z].oldHash[i] <== simp[izx+i];
            izx++;
        }
        for (var i = 0; i < 2**(z-1); i++) {
            simp[izx+i] <== solvent[n-z].newHash[i];
            izx++;
        }
    }
    assert(izx == 2**(n+1) - 1);
    root <== simp[2**(n+1)-2];
}

template MerkleTreeInclusionProof(n) {
    signal input leaf;
    signal input path_elements[n];
    signal input path_index[n]; // path index are 0's and 1's indicating whether the current element is on the left or right
    signal output root; // note that this is an OUTPUT signal

    //[assignment] insert your code here to compute the root from a leaf and elements along the path
    signal product[n+1];
    component poseidonI[n];
    product[0] <== leaf;

    for (var i = 0; i < n; i++) {
        poseidonI[i] = Poseidon(2);

        assert( (path_index[i] == 0) || (path_index[i] == 1) );

        poseidonI[i].inputs[1] <== (product[i] - path_elements[i]) * path_index[i] + path_elements[i];
        poseidonI[i].inputs[0] <== (path_elements[i] - product[i]) * path_index[i] + product[i];
        product[i+1] <== poseidonI[i].out;
    }
    
    root <== product[n];
}
