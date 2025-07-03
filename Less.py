from hashlib import sha256
import os
import random
import numpy as np
from sage.all import GF, matrix
from collections import deque
import hashlib

# Helper function for deterministic sampling
def sample_without_replacement(n, k, seed):
    """Sample k distinct indices from [0, n-1] using seed deterministically"""
    indices = list(range(n))
    selected = []
    seed_bytes = seed
    
    for i in range(k):
        # Compute hash for this selection round
        data = seed_bytes + i.to_bytes(4, 'big')
        h = sha256(data).digest()
        num = int.from_bytes(h, 'big')
        
        # Select index from remaining indices
        j = num % (n - i)
        selected.append(indices[j])
        del indices[j]
        
    return selected

# Monomial matrix generation
def generate_monomial_matrix_fixed(self, seed, size):
    """Generate random monomial matrix with non-zero diagonals"""
    # Generate permutation indices using Fisher-Yates shuffle
    indices = list(range(size))
    for i in range(size-1, 0, -1):
        # Generate random index in [0, i]
        data = seed + b'perm' + i.to_bytes(4, 'big')
        h = sha256(data).digest()
        num = int.from_bytes(h, 'big')
        j = num % (i+1)
        indices[i], indices[j] = indices[j], indices[i]
    
    # In GF(2), non-zero diagonal must be 1
    diag_elements = [self.Fq(1) for _ in range(size)]
    
    # Build monomial matrix
    M = matrix(self.Fq, size, size)
    for i in range(size):
        M[i, indices[i]] = diag_elements[i]
    return M

# 1. Key Generation Implementation
class LESSKeygen:
    def __init__(self, q, k, n, s, lambd=128):
        self.q = q
        self.k = k
        self.n = n
        self.s = s
        self.lambd = lambd
        self.Fq = GF(q)

    def prng(self, seed, count):
        elements = []
        j = 0
        while j < count:
            data = seed + j.to_bytes(4, 'big')
            h = sha256(data).digest()
            num = int.from_bytes(h, 'big')
            elem = num % self.q
            if elem == 0 and self.q != 2:  # Handle GF(2) zero case
                elem = self.Fq(1)
            elements.append(self.Fq(elem))
            j += 1
        return elements

    def generate_matrix_from_seed(self, seed, nrows, ncols):
        total_elements = nrows * ncols
        elements = self.prng(seed, total_elements)
        return matrix(self.Fq, nrows, ncols, elements)

    def generate_full_rank_rref(self, seed, nrows, ncols):
        counter = 0
        while True:
            h_seed = seed + counter.to_bytes(4, 'big')
            M = self.generate_matrix_from_seed(h_seed, nrows, ncols)
            M_rref = M.rref()
            if M_rref.rank() == nrows:
                return M_rref
            counter += 1

    generate_monomial_matrix = generate_monomial_matrix_fixed

    def compress_rref(self, M):
        pivots = M.pivots()
        non_pivot_cols = sorted(set(range(self.n)) - set(pivots))
        non_pivot_mat = M.matrix_from_columns(non_pivot_cols)
        return (non_pivot_cols, non_pivot_mat)

    def keygen(self):
        seed0 = os.urandom(self.lambd // 8)
        G0 = self.generate_full_rank_rref(seed0, self.k, self.n)
        
        sk = []
        pk = [seed0]
        
        for i in range(1, self.s):
            seed_i = os.urandom(self.lambd // 8)
            Q = self.generate_monomial_matrix(seed_i, self.n)
            Qi = Q.inverse()
            
            Gi = (G0 * Qi).rref()
            comp_rep = self.compress_rref(Gi)
            
            sk.append(seed_i)
            pk.append(comp_rep)
        
        return (sk, pk)
    
    def print_private_key(self, sk):
        """Print private key in human-readable format"""
        print("\nPrivate Key:")
        for i, seed in enumerate(sk):
            print(f"  Seed {i+1}: {seed.hex()}")
    
    def print_public_key(self, pk):
        """Print public key in human-readable format"""
        print("\nPublic Key:")
        print(f"  seed0: {pk[0].hex()}")
        for i in range(1, len(pk)):
            non_pivot_cols, non_pivot_mat = pk[i]
            print(f"  G{i}:")
            print(f"    Non-pivot columns: {non_pivot_cols}")
            print(f"    Non-pivot matrix:\n{non_pivot_mat.str()}")

# 2. Signing Implementation
class LESSSigner:
    def __init__(self, q, k, n, s, t, omega, lambd=128):
        self.q = q
        self.k = k
        self.n = n
        self.s = s
        self.t = t
        self.omega = omega
        self.lambd = lambd
        self.Fq = GF(q)

    def prng(self, seed, count):
        elements = []
        j = 0
        while j < count:
            data = seed + j.to_bytes(4, 'big')
            h = sha256(data).digest()
            num = int.from_bytes(h, 'big')
            elem = num % self.q
            if elem == 0 and self.q != 2:  # Handle GF(2) zero case
                elem = self.Fq(1)
            elements.append(self.Fq(elem))
            j += 1
        return elements

    generate_monomial_matrix = generate_monomial_matrix_fixed

    def seed_tree_leaves(self, root_seed, salt, num_leaves):
        leaves = []
        queue = deque([(root_seed, 0)])
        max_depth = int(np.ceil(np.log2(num_leaves)))
        
        while queue and len(leaves) < num_leaves:
            current_seed, depth = queue.popleft()
            left_seed = sha256(current_seed + b'left' + salt + depth.to_bytes(4, 'big')).digest()
            right_seed = sha256(current_seed + b'right' + salt + depth.to_bytes(4, 'big')).digest()
            
            if depth < max_depth - 1:
                queue.append((left_seed, depth + 1))
                queue.append((right_seed, depth + 1))
            else:
                leaves.append(left_seed)
                if len(leaves) < num_leaves:
                    leaves.append(right_seed)
        return leaves[:num_leaves]

    def prepare_digest_input(self, G0, Q_tilde):
        V_i = G0 * Q_tilde
        V_i_rref = V_i.rref()
        pivots = V_i_rref.pivots()
        non_pivot_cols = sorted(set(range(self.n)) - set(pivots))
        non_pivot_mat = V_i_rref.matrix_from_columns(non_pivot_cols)
        return non_pivot_mat  # Return only the matrix for hashing

    def sign(self, sk, pk, msg):
        seed0 = pk[0]
        keygen = LESSKeygen(self.q, self.k, self.n, self.s, self.lambd)
        G0 = keygen.generate_full_rank_rref(seed0, self.k, self.n)
        
        root_seed = os.urandom(self.lambd // 8)
        salt = os.urandom(self.lambd // 8)
        seeds = self.seed_tree_leaves(root_seed, salt, self.t)
        
        V_matrices = []  # Store matrices for hashing
        Q_tildes = []
        
        for i in range(self.t):
            Q_tilde = self.generate_monomial_matrix(seeds[i], self.n)
            Q_tildes.append(Q_tilde)
            V_i = self.prepare_digest_input(G0, Q_tilde)
            V_matrices.append(V_i)
        
        # Compute digest using consistent representation
        data = b""
        for mat in V_matrices:
            data += mat.str().encode()  # Only matrix content
        data += msg.encode() + salt
        d = sha256(data).digest()
        
        # Deterministic challenge generation
        non_zero_indices = sample_without_replacement(self.t, self.omega, d)
        x = [1 if i in non_zero_indices else 0 for i in range(self.t)]
        
        fsp_list = []
        resp_count = 0
        
        for i in range(self.t):
            if x[i] != 0:
                priv_seed = sk[resp_count]
                Q_priv = self.generate_monomial_matrix(priv_seed, self.n)
                response_matrix = Q_priv * Q_tildes[i]
                
                perm = []
                diag = []
                for row in range(response_matrix.nrows()):
                    for col in range(response_matrix.ncols()):
                        if response_matrix[row, col] != 0:
                            perm.append(col)
                            diag.append(response_matrix[row, col])
                            break
                
                fsp_list.append((perm, diag))
                resp_count += 1
        
        return {
            "salt": salt,
            "root_seed": root_seed,
            "fsp_list": fsp_list,
            "digest": d
        }
    
    def print_signature(self, signature):
        """Print signature components"""
        print("\nSignature:")
        print(f"  salt: {signature['salt'].hex()}")
        print(f"  root_seed: {signature['root_seed'].hex()}")
        print(f"  digest: {signature['digest'].hex()}")
        print("  Responses:")
        for i, (perm, diag) in enumerate(signature['fsp_list']):
            print(f"    Response {i+1}:")
            print(f"      Permutation: {perm}")
            print(f"      Diagonal: {[int(d) for d in diag]}")

# 3. Verification Implementation
class LESSVerifier:
    def __init__(self, q, k, n, s, t, omega, lambd=128):
        self.q = q
        self.k = k
        self.n = n
        self.s = s
        self.t = t
        self.omega = omega
        self.lambd = lambd
        self.Fq = GF(q)

    def prng(self, seed, count):
        elements = []
        j = 0
        while j < count:
            data = seed + j.to_bytes(4, 'big')
            h = sha256(data).digest()
            num = int.from_bytes(h, 'big')
            elem = num % self.q
            if elem == 0 and self.q != 2:  # Handle GF(2) zero case
                elem = self.Fq(1)
            elements.append(self.Fq(elem))
            j += 1
        return elements

    def generate_full_rank_rref(self, seed, nrows, ncols):
        counter = 0
        while True:
            h_seed = seed + counter.to_bytes(4, 'big')
            M = self.generate_matrix_from_seed(h_seed, nrows, ncols)
            M_rref = M.rref()
            if M_rref.rank() == nrows:
                return M_rref
            counter += 1

    def generate_matrix_from_seed(self, seed, nrows, ncols):
        total_elements = nrows * ncols
        elements = self.prng(seed, total_elements)
        return matrix(self.Fq, nrows, ncols, elements)

    generate_monomial_matrix = generate_monomial_matrix_fixed

    def expand_to_monomial(self, rsp):
        perm, diag = rsp
        size = len(perm)
        M = matrix(self.Fq, size, size)
        for i in range(size):
            M[i, perm[i]] = diag[i]
        return M

    def expand_rref(self, non_pivot_cols, non_pivot_mat, n, k):
        pivot_cols = sorted(set(range(n)) - set(non_pivot_cols))
        M = matrix(self.Fq, k, n)
        for i, col in enumerate(pivot_cols):
            M[i, col] = 1
        for j, col in enumerate(non_pivot_cols):
            M.set_column(col, non_pivot_mat.column(j))
        return M

    def prepare_digest_input(self, G0, Q_bar):
        V_i = G0 * Q_bar
        V_i_rref = V_i.rref()
        pivots = V_i_rref.pivots()
        non_pivot_cols = sorted(set(range(self.n)) - set(pivots))
        non_pivot_mat = V_i_rref.matrix_from_columns(non_pivot_cols)
        return non_pivot_mat  # Same as signer

    def rebuild_seed_tree_leaves(self, root_seed, salt, num_leaves):
        leaves = []
        for i in range(num_leaves):
            data = root_seed + salt + i.to_bytes(4, 'big')
            leaf = sha256(data).digest()
            leaves.append(leaf)
        return leaves

    def verify(self, pk, sigma, msg):
        salt = sigma['salt']
        root_seed = sigma['root_seed']
        fsp_list = sigma['fsp_list']
        d = sigma['digest']
        
        seed0 = pk[0]
        keygen = LESSKeygen(self.q, self.k, self.n, self.s, self.lambd)
        G0 = keygen.generate_full_rank_rref(seed0, self.k, self.n)
        
        # Deterministic challenge generation (same as signer)
        non_zero_indices = sample_without_replacement(self.t, self.omega, d)
        x = [1 if i in non_zero_indices else 0 for i in range(self.t)]
        
        seeds = self.rebuild_seed_tree_leaves(root_seed, salt, self.t)
        
        V_matrices = []
        resp_index = 0
        
        for i in range(self.t):
            if x[i] == 0:
                Q_bar = self.generate_monomial_matrix(seeds[i], self.n)
                V_i = self.prepare_digest_input(G0, Q_bar)
                V_matrices.append(V_i)
            else:
                Q_bar = self.expand_to_monomial(fsp_list[resp_index])
                resp_index += 1
                comp_G = pk[x[i]]
                G_i = self.expand_rref(comp_G[0], comp_G[1], self.n, self.k)
                V_i = self.prepare_digest_input(G_i, Q_bar)
                V_matrices.append(V_i)
        
        # Compute hash same as signer
        data = b""
        for V_i in V_matrices:
            data += V_i.str().encode()
        data += msg.encode() + salt
        d_prime = sha256(data).digest()
        
        return d_prime == d
    
    def print_verification_result(self, is_valid, msg):
        """Print verification result"""
        print(f"\nVerification for '{msg[:20]}...':")
        print("  Result:", "VALID" if is_valid else "INVALID")

# Full LESS Test
if __name__ == "__main__":
    # Consistent parameters
    q = 2     # GF(2)
    k = 2     # Rows
    n = 3     # Columns
    s = 4     # Matrices in public key
    t = 4     # Seed tree leaves
    omega = 2 # Non-zero responses
    lambd = 128
    msg = "This is a test message for the LESS signature scheme"

    print("="*70)
    print("LESS Signature Scheme - Implementation")
    print("="*70)
    print(f"Parameters: GF({q}), k={k}, n={n}, s={s}, t={t}, ω={omega}")
    print(f"Message: '{msg}'")
    print("-"*70)
    
    # 1. Key Generation
    print("\n[1/3] Key Generation:")
    keygen = LESSKeygen(q, k, n, s, lambd)
    sk, pk = keygen.keygen()
    keygen.print_private_key(sk)
    keygen.print_public_key(pk)
    
    # 2. Signing
    print("\n[2/3] Signing:")
    signer = LESSSigner(q, k, n, s, t, omega, lambd)
    signature = signer.sign(sk, pk, msg)
    signer.print_signature(signature)
    
    # 3. Verification
    print("\n[3/3] Verification:")
    verifier = LESSVerifier(q, k, n, s, t, omega, lambd)
    
    # Original message verification
    is_valid = verifier.verify(pk, signature, msg)
    verifier.print_verification_result(is_valid, msg)
    
    # Tampered message test
    tampered_msg = msg + " (tampered)"
    is_valid_tampered = verifier.verify(pk, signature, tampered_msg)
    verifier.print_verification_result(is_valid_tampered, tampered_msg)
    
    print("\n" + "="*70)
    print("Test Summary:")
    print(f"  Original message valid: {'Yes' if is_valid else 'No'}")
    print(f"  Tampered message valid: {'Yes' if is_valid_tampered else 'No'}")
    print("="*70)
