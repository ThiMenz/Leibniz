using System.Diagnostics;
using System.Numerics;
using System.Text;

namespace IDEAS
{
    public class GGRM_GraphNodeSubsetTuple
    {
        public static Dictionary<GGRM_GraphNodeSubsetTuple, List<GGRM_GraphNodeSubsetTuple>> allOriginalLinks = new Dictionary<GGRM_GraphNodeSubsetTuple, List<GGRM_GraphNodeSubsetTuple>>();

        public GGRM_N_Subset originals = new(1, 0), values = new(1, 0);
        public GGRM_GraphNodeSubsetTuple rootTupleRef;
        public GGRM_GraphNode nodeRef;

        public GGRM_GraphNodeSubsetTuple(GGRM_GraphNode node, GGRM_N_Subset pOriginalsAndValues)
        {
            originals = pOriginalsAndValues;
            values = pOriginalsAndValues;
            nodeRef = node;
            rootTupleRef = this;
            allOriginalLinks.Add(this, new());
        }


        public GGRM_GraphNodeSubsetTuple(GGRM_GraphNode node, GGRM_GraphNodeSubsetTuple rootTuple, GGRM_N_Subset pOriginals, GGRM_N_Subset pValues)
        {
            originals = pOriginals;
            values = pValues;
            rootTupleRef = rootTuple;
            nodeRef = node;
            allOriginalLinks[rootTupleRef].Add(this);
        }
        public override string ToString()
        {
            return $"({originals}->{values})";
        }

    }

    public class GGRM_GraphNode
    {
        public static double staticUncertaintyUntil = 0;
        public static GGRM_GraphNode root;

        public List<GGRM_GraphNodeSubsetTuple> subsetTuples = new();

        public GGRM_GraphNode[] childNodes = new GGRM_GraphNode[4];
        public GGRM_GraphNode? parent = null;

        public enum GraphDirection { pos3, pos2, neg2, neg3, none }
        public GraphDirection previousGraphDir = GraphDirection.none;

        public void GenerateChildren()
        {
            GraphDirection[] tDirList = { GraphDirection.neg3, GraphDirection.neg2, GraphDirection.pos2, GraphDirection.pos3 };

            foreach (GGRM_GraphNodeSubsetTuple subsetTuple in subsetTuples)
            {
                if (subsetTuple.values.a < subsetTuple.originals.a) continue;
                foreach (GraphDirection dir in tDirList)
                    if (previousGraphDir != (3 - dir)) AddChild(subsetTuple, dir);
            }
        }

        public void AddChild(GGRM_GraphNodeSubsetTuple subsetTuple, GraphDirection dir)
        {
            GGRM_N_Subset values = subsetTuple.values, originals = subsetTuple.originals, tmp;
            GGRM_GraphNode newNode = childNodes[(int)dir] == null ? new() : childNodes[(int)dir];
            GGRM_GraphNodeSubsetTuple newTuple = new(newNode, subsetTuple.rootTupleRef, new(1, 0), new(1, 0));
            switch (dir)
            {
                case GraphDirection.pos3:
                    tmp = (values % 2 == 1)[0];
                    if (tmp.a == 0) return;
                    newTuple.originals = tmp * originals;
                    newTuple.values = tmp * values * 3 + 1;
                    break;
                case GraphDirection.neg3:
                    tmp = (values % 6 == 4)[0];
                    if (tmp.a == 0) return;
                    newTuple.originals = tmp * originals;
                    newTuple.values = (tmp * values - 1) / 3;
                    break;
                case GraphDirection.pos2:
                    newTuple.originals = originals;
                    newTuple.values = values * 2;
                    break;
                case GraphDirection.neg2:
                    tmp = (values % 2 == 0)[0];
                    if (tmp.a == 0) return;
                    newTuple.originals = tmp * originals;
                    newTuple.values = tmp * values / 2;
                    break;
            }
            newNode.parent = this;
            newNode.previousGraphDir = dir;
            newNode.subsetTuples.Add(newTuple);
            childNodes[(int)dir] = newNode;
        }
        public bool CheckForUpperCutoffs(int remainingDepth)
        {
            bool b = false;
            foreach (GGRM_GraphNodeSubsetTuple subsetTuple in subsetTuples.ToArray())
            {
                if ((subsetTuple.values.a / subsetTuple.originals.a) > BigInteger.Pow(3, remainingDepth))
                    subsetTuples.Remove(subsetTuple);
            }

            return b;
        }


        public bool CheckForLowerCutoffs()
        {
            bool foundCutoff = false;

            foreach (GGRM_GraphNodeSubsetTuple subsetTuple in subsetTuples)
            {
                if (subsetTuple.values.a < subsetTuple.originals.a)
                {
                    bool b = false;
                    foreach (GGRM_GraphNodeSubsetTuple rule in GGRM.allNewRules)
                        if (subsetTuple.originals == rule.originals)
                            b = true;

                    if (!b)
                    {
                        Console.WriteLine("NEW RULE: " + subsetTuple.originals + "\n");

                        foundCutoff = true;
                        GGRM.allNewRules.Add(subsetTuple);
                    }
                }
            }

            return foundCutoff;
        }

        public void ApplyNewRule(GGRM_GraphNodeSubsetTuple subsetTuple)
        {
            GGRM_N_Subset newRule = subsetTuple.originals;

            List<GGRM_N_Subset> splits = new List<GGRM_N_Subset>();

            double tDiff = (double)(newRule.b - newRule.b % newRule.a);
            if (tDiff > staticUncertaintyUntil) staticUncertaintyUntil = tDiff;

            newRule.b = newRule.b % newRule.a;
            List<GGRM_GraphNodeSubsetTuple> newRootSubsets = new();
            foreach (GGRM_GraphNodeSubsetTuple rootTuple in root.subsetTuples)
            {
                for (BigInteger i = 0; i < subsetTuple.originals.a; i++)
                {
                    if (subsetTuple.originals.b == i) continue;

                    GGRM_N_Subset tmpPotNewSubset = new GGRM_N_Subset(subsetTuple.originals.a, i);
                    GGRM_N_Subset t = rootTuple.originals & tmpPotNewSubset;

                    if (t.a != 0)
                    {
                        bool foundEqualOrPartialSubset = false;
                        foreach (GGRM_N_Subset g in splits)
                        {
                            GGRM_N_Subset gANDt = g & t;
                            if (gANDt == g)
                            {
                                foundEqualOrPartialSubset = true;
                                break;
                            }
                            else if (gANDt == t)
                            {
                                splits.Add(t);
                                splits.Remove(g);
                                foundEqualOrPartialSubset = true;
                                break;
                            }
                        }

                        if (!foundEqualOrPartialSubset)
                        {
                            splits.Add(t);
                        }
                    }
                }
            }

            double tStaticUncertainty = (double)(subsetTuple.originals.b - subsetTuple.values.b) / (double)(subsetTuple.values.a - subsetTuple.originals.a);
            if (tStaticUncertainty > staticUncertaintyUntil) staticUncertaintyUntil = tStaticUncertainty;

            GGRM_GraphNodeSubsetTuple.allOriginalLinks.Clear();
            GGRM_GraphNode newRootNode = new();
            root = newRootNode;
            foreach (GGRM_N_Subset subset in splits)
            {
                GGRM_GraphNodeSubsetTuple newBase = new(root, subset);
                //GGRM_GraphNodeSubsetTuple.allOriginalLinks.Add(newBase, new());
                newRootNode.subsetTuples.Add(newBase);
            }
        }

        #region | TREE STRING CONVERSION |

        public override string ToString()
        {
            var sb = new StringBuilder();
            // start the recursion at the root; we use 'none' so the root itself has no incoming label
            BuildAsciiTree(sb, "", true, GraphDirection.none);
            return sb.ToString();
        }

        private void BuildAsciiTree(StringBuilder sb, string indent, bool isLast, GraphDirection incomingDir)
        {
            // 1) branch prefix
            sb.Append(indent);
            sb.Append(isLast ? "+- " : "|- ");

            // 2) edge label
            if (incomingDir != GraphDirection.none)
            {
                string label = incomingDir switch
                {
                    GraphDirection.pos3 => "*3",
                    GraphDirection.neg3 => "/3",
                    GraphDirection.pos2 => "*2",
                    GraphDirection.neg2 => "/2",
                    _ => "?"
                };
                sb.Append($"[{label}] ");
            }

            // 3) list out this node’s subsetTuples
            if (subsetTuples.Count == 0)
            {
                sb.AppendLine("(no tuples)");
            }
            else
            {
                // e.g. ( {1n+0}→{3n+1} , {2n+1}→{4n+2} )
                sb.AppendLine(string.Join(" , ", subsetTuples.Select(t => t.ToString())));

            }

            // 4) compute the next indent
            string childIndent = indent + (isLast ? "   " : "|  ");

            // 5) recurse for all four possible children in their array positions
            for (int dirIndex = 0; dirIndex < childNodes.Length; dirIndex++)
            {
                var child = childNodes[dirIndex];
                if (child == null) continue;

                bool lastChild = true;
                // look ahead to see if there's any non-null beyond this
                for (int j = dirIndex + 1; j < childNodes.Length; j++)
                    if (childNodes[j] != null) lastChild = false;

                child.BuildAsciiTree(sb, childIndent, lastChild, child.previousGraphDir);
            }
        }

        #endregion
    }

    public class GGRM_N_Subset
    {
        public BigInteger a, b, mod; //mod is temp

        public GGRM_N_Subset(BigInteger pA, BigInteger pB)
        {
            a = pA; b = pB;
        }

        public GGRM_N_Subset(BigInteger pA, BigInteger pB, BigInteger pM)
        {
            a = pA; b = pB; mod = pM;
        }

        public bool Mod(BigInteger modulu, BigInteger result)
        {
            return Mod(this, modulu, result).a != 0; //((a % modulu) + (b % modulu)) % modulu == result;
        }

        public static GGRM_N_Subset Mod(GGRM_N_Subset subset, BigInteger m, BigInteger k)
        {
            BigInteger a = subset.a, b = subset.b;
            BigInteger t = k - (b % m) + ((b % m) > k ? 6 : 0);
            if ((a % m) != 0)
                return t % (a % m) == 0 ? new GGRM_N_Subset(m / BigInteger.GreatestCommonDivisor(a, m), t / (a % m)) : new GGRM_N_Subset(0, 0);
            else
                return (a + b) % m == k ? new GGRM_N_Subset(1, 0) : new GGRM_N_Subset(0, 0);
        }
        public static bool operator ==(GGRM_N_Subset subset, GGRM_N_Subset subset2)
        {
            return subset.a == subset2.a && subset.b == subset2.b;
        }
        public static bool operator !=(GGRM_N_Subset subset, GGRM_N_Subset subset2)
        {
            return subset.a != subset2.a || subset.b != subset2.b;
        }
        public static List<GGRM_N_Subset> operator ==(GGRM_N_Subset subset, BigInteger value)
        {
            return new List<GGRM_N_Subset>() { Mod(subset, subset.mod, value) };
        }

        public static List<GGRM_N_Subset> operator !=(GGRM_N_Subset subset, BigInteger value)
        {
            List<GGRM_N_Subset> rList = new List<GGRM_N_Subset>();
            for (BigInteger i = 0; i < subset.mod; i++)
            {
                if (i == value) continue;
                GGRM_N_Subset tSubset = Mod(subset, subset.mod, i);
                if (tSubset.a != 0) rList.Add(Mod(subset, subset.mod, i));
            }
            return rList;
        }

        public static GGRM_N_Subset operator &(GGRM_N_Subset set1, GGRM_N_Subset set2)
        {
            return Mod(set1, set2.a, set2.b) * set1;
        }

        public override bool Equals(object? obj) { return base.Equals(obj); }

        public override int GetHashCode() { return base.GetHashCode(); }

        public override string ToString() { return "{" + a + "n + " + b + "}"; }


        #region | TRIVIAL OPERATORS |

        public static GGRM_N_Subset operator %(GGRM_N_Subset subset, BigInteger value) { return new GGRM_N_Subset(subset.a, subset.b, value); }

        public static GGRM_N_Subset operator +(GGRM_N_Subset subset, BigInteger value) { return new GGRM_N_Subset(subset.a, subset.b + value); }

        public static GGRM_N_Subset operator *(GGRM_N_Subset inner, GGRM_N_Subset outer) { return new GGRM_N_Subset(inner.a * outer.a, inner.b * outer.a + outer.b); }

        public static GGRM_N_Subset operator *(GGRM_N_Subset subset, BigInteger value) { return new GGRM_N_Subset(subset.a * value, subset.b * value); }

        public static GGRM_N_Subset operator -(GGRM_N_Subset subset, BigInteger value) { return new GGRM_N_Subset(subset.a, subset.b - value); }

        public static GGRM_N_Subset operator /(GGRM_N_Subset subset, BigInteger value) { return new GGRM_N_Subset(subset.a / value, subset.b / value); }

        #endregion
    }

    public static class GGRM
    {
        public static void Main(string[] args)
        {
            const int MAX_DEPTH = 12;

            Stopwatch sw = Stopwatch.StartNew();

            int iteration = 0, furthestDepth = 1;
            cutoffFound = true;

            while (cutoffFound)
            {

                cutoffFound = false;
                for (int i = furthestDepth; i <= MAX_DEPTH; i++)
                {
                    Console.WriteLine(i);

                    nodeCount = 0;
                    //GGRM_GraphNodeSubsetTuple.allOriginalLinks.Clear();
                    GGRM_GraphNode beginNode = GGRM_GraphNode.root;

                    if (iteration == 0)
                    {
                        beginNode = GGRM_GraphNode.root = new();
                        beginNode.subsetTuples = new List<GGRM_GraphNodeSubsetTuple>() { new GGRM_GraphNodeSubsetTuple(beginNode, new(1, 0)) };
                    }

                    //if (i == furthestDepth) Console.WriteLine(beginNode);

                    RecursiveTreeGeneration(i, beginNode);

                    foreach (GGRM_GraphNodeSubsetTuple rule in allNewRules) beginNode.ApplyNewRule(rule);
                    allNewRules.Clear();

                    if (furthestDepth < i) furthestDepth = i;
                    if (cutoffFound || MAX_DEPTH == furthestDepth)
                    {
                        double totalPercentage = 0;
                        foreach (GGRM_GraphNodeSubsetTuple subsetT in beginNode.subsetTuples) totalPercentage += (1.0d / (double)subsetT.originals.a);

                        //foreach (GGRM_N_Subset subset in cutoffPossibilities) Console.WriteLine(subset);

                        Console.WriteLine($"{++iteration}. Iteration (depth = {furthestDepth}, " +
                        $"uncertaintyThreshold = {GGRM_GraphNode.staticUncertaintyUntil}, " +
                        $"rootSubsetCount = {beginNode.subsetTuples.Count}, " +
                        $"nodeCount = {nodeCount}, " +
                        $"remainingNaturalsSize = {totalPercentage}):");
                        //Console.WriteLine(beginNode);
                        Console.WriteLine();
                        Console.WriteLine();
                        break;
                    }
                }
            }

            sw.Stop();

            Console.WriteLine($"Elapsed Time: {sw.ElapsedMilliseconds}ms");
        }


        public static bool cutoffFound = true;
        //private static List<GGRM_N_Subset> remainingPossibilities = new();
        private static long nodeCount = 0;
        public static List<GGRM_GraphNodeSubsetTuple> allNewRules = new();

        public static void RecursiveTreeGeneration(int depth, GGRM_GraphNode node)
        {
            nodeCount++;

            if (node == null) return;

            if (node.CheckForLowerCutoffs()) cutoffFound = true;

            if (depth == 0 || cutoffFound) return;

            node.CheckForUpperCutoffs(depth);

            node.GenerateChildren();
            foreach (GGRM_GraphNode child in node.childNodes)
                RecursiveTreeGeneration(depth - 1, child);
        }
    }
}
