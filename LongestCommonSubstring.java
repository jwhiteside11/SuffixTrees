
// dp is too slow (O(n*m)) for n = m = 10^5, implement suffix tree instead (O(n+m))
// build suffix tree with Ukkonen's algorithm (O(n), O(m)), find LCA

// Better -> build suffix array directly with DC3 O(n + m) time, less extra space
// DC3 steps:
//  1) Convert to int alphabet, append 000 to sequence
//  2) Collect sample indices (i%3 == 1 | i%3 == 2), and non-sample indices (i%3 == 0)
//
//  3) Use radix sort to sort suffices at sample indices by first three letters
//      » Once sorted, generate lexicographical names: samp[i] != samp[i+1] ? count++ : count;
//      » If there are duplicate names, recursively call DC3 on (name array + 000)
//
//  4) If recursive call was made, generate sorted sample array using return value (invert)
//      » samps[returnedSA[i]] = i + 1;
//     else just use names from initial radix sort
//      » samps[names[i] - 1] = i;
//
//  5) Sort non-sample suffices using radix sort
//
//  6) Merge sorted sample (B12) and sorted non-sample (B0) arrays
//      » Two cases: compare(B0, B1) and compare(B0, B2)
//          » compare(B0, B1) -> compare(b0, b1) == 0 ? compare(b0+1, b1+1) : comp0;
//          » compare(B0, B2) -> compare(b0, b2) == 0 ? compare(b0+1, b2+1) == 0 ?
//                                              compare(b0+2, b2+2) : comp0;
//      » Note: In any case, our recursive calls guarantee no ties in the comparison stage
//  7) Output the merged array (suffix array)

// Then the LCS can be found intuitively using the suffix array and an LCP array in O(n + m) time

public class LongestCommonSubstring {

    public int findLCS(String s, String t) {

        int n = s.length();
        int m = t.length();
        if (s.contains(t)) return t.length();
        if (t.contains(s)) return s.length();

        String concat = s + "$" + t;
        int cc = n + m + 1;
        int[] digitized = encodeString(concat, cc);
        int[] suffixArray = suffixArray(digitized, cc, 255);
        int[] lcp = lcp(concat, suffixArray, cc);

        // Find longest common substring from suffix array and lcp
        int maxLen = 0;
        for (int i = 1; i < m + n; ++i) {
            if ((suffixArray[i] < n && suffixArray[i+1] < n) || (suffixArray[i] > n && suffixArray[i+1] > n)) continue;
            maxLen = Math.max(lcp[i], maxLen);
        }
        return maxLen;
    }

// Kasai's algo O(n) -> http://web.cs.iastate.edu/~cs548/references/linear_lcp.pdf 
//                      https://codeforces.com/blog/entry/12796
// Uses suffix array and inverted SA (rank) to find lcp array in linear time

    public int[] lcp(String s, int[] sA, int n) {
        int[] rank = new int[n];
        int[] lcp = new int[n];
        int k = 0;

        for (int i = 0; i < n; ++i) rank[sA[i]] = i;
        for (int i = 0; i < n; ++i) {
            if (rank[i] == n - 1) {
                k = 0;
                continue;
            }
            int j = sA[rank[i] + 1];
            while (i + k < n && j + k < n && s.charAt(i+k) == s.charAt(j+k)) ++k;
            lcp[rank[i]] = k;
            if (k != 0) --k;
        }
        return lcp;
    }

// DC3 algo O(n) -> https://www.cs.helsinki.fi/u/tpkarkka/publications/jacm05-revised.pdf 
//                  http://www.mi.fu-berlin.de/wiki/pub/ABI/SS13Lecture3Materials/script.pdf

    public int[] suffixArray(int[] input, int n, int K) {
        int n0 = (n + 2) / 3, n1 = (n + 1) / 3, n2 = n / 3, n02 = n0 + n2;
        int[] s12 = new int[n02 + 3], sA12 = new int[n02 + 3];
        int[] s0 = new int[n0], sA0 = new int[n0];

        // populate s12 with i % 3 != 0 indices
        for (int i = 0, j = 0; i < n + (n0 - n1); ++i) if (i % 3 != 0) s12[j++] = i;

        // radix sort first three characters of each sample prefix
        radixPass(input, s12, sA12, 2, n02, K); // input, output, offset, length, radix
        radixPass(input, sA12, s12, 1, n02, K);
        radixPass(input, s12, sA12, 0, n02, K);

        // find "lexicographical names" for triples (just rank radix sort results)
        int name = 0, c0 = -1, c1 = -1, c2 = -1;
        for (int i = 0; i < n02; ++i) {
            if (input[sA12[i]] != c0 || input[sA12[i]+1] != c1 || input[sA12[i]+2] != c2) {
                ++name;
                c0 = input[sA12[i]];
                c1 = input[sA12[i] + 1];
                c2 = input[sA12[i] + 2];
            }
            if (sA12[i] % 3 == 1) s12[sA12[i]/3] = name;
            else s12[sA12[i]/3 + n0] = name;
        }

        // recurse if not all names are unique, else directly build the suffix array from names
        if (name < n02) {
            sA12 = suffixArray(s12, n02, name);
            for (int i = 0; i < n02; ++i) s12[sA12[i]] = i + 1; // update with unique names
        }
        else {
            for (int i = 0; i < n02; ++i) sA12[s12[i] - 1] = i; // generate from radix
        }

        // sort i % 3 == 0 indices by first character
        for (int i = 0, j = 0; i < n02; ++i) if (sA12[i] < n0) s0[j++] = 3 * sA12[i];
        radixPass(input, s0, sA0, 0, n0, K);

        // merge sorted sA0 and sorted sA12
        int[] output = new int[n];
        for (int u = n0 - n1, v = 0, x = 0; x < n; ++x) {
            int i = sA12[u] < n0 ? 3 * sA12[u] + 1 : 3 * (sA12[u] - n0) + 2;
            int j = sA0[v];
            if (sA12[u] < n0 ? leq(input[i], s12[sA12[u]+n0], input[j], s12[j/3]):
                    leq(input[i], input[i+1], s12[sA12[u]-n0+1], input[j], input[j+1], s12[j/3 + n0])) {
                // sA12 has smaller suffix
                output[x] = i;
                ++u;
                if (u == n02) {
                    for (x++; v < n0; v++, x++) output[x] = sA0[v];
                }
            } else {
                // sA0 has smaller suffix
                output[x] = j;
                ++v;
                if (v == n0) {
                    for (x++; u < n02; u++, x++) output[x] = sA12[u] < n0 ? 3*sA12[u] + 1 : 3*(sA12[u] - n0) + 2;
                }
            }
        }
        return output;
    }

    private void radixPass(int[] nums, int[] input, int[] output, int offset, int n, int K) {
        int[] count = new int[K + 1];
        for (int i = 0; i < n; ++i) count[nums[input[i] + offset]]++;
        for (int i = 0, sum = 0; i <= K; ++i) {
            int t = count[i];
            count[i] = sum;
            sum += t;
        }
        for (int i = 0; i < n; ++i) output[count[nums[input[i] + offset]]++] = input[i];
    }

    private boolean leq(int a1, int a2, int b1, int b2) {
        return a1 < b1 || (a1 == b1 && a2 <= b2);
    }

    private boolean leq(int a1, int a2, int a3, int b1, int b2, int b3) {
        return a1 < b1 || (a1 == b1 && leq(a2, a3, b2, b3));
    }

    private int[] encodeString(String s, int len) {
        int[] out = new int[len + 3];
        for (int i = 0; i < len; ++i) {
            out[i] = s.charAt(i);
        }
        return out;
    }
}
