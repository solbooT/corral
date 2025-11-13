﻿using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using VC;
using cba.Util;
using Microsoft.Boogie.GraphUtil;
using System.Threading.Tasks;

namespace CoreLib
{
    /****************************************
    *           Pseudo macros               *
    ****************************************/

    // TODO: replace this with conventional functions
    public class MacroSI
    {
        public static void PRINT(int lvl, string s, params object[] args)
        {
            if (StratifiedInlining.StratifiedInliningVerbose >= lvl)
                Console.WriteLine(s, args);
        }

        public static void PRINT(string s, params object[] args) { PRINT(0, s, args); }

        public static void PRINT_DETAIL(string s, params object[] args) { PRINT(1, s, args); }

        public static void PRINT_DEBUG(string s, params object[] args) { PRINT(2, s, args); }
    }

    /****************************************
    * Classes for diverse program analyses *
    ****************************************/

    /* locates (user-) assertions in the code */
    class LocateAsserts
    {

        public LocateAsserts()
            : base()
        {
        }

        public List<Procedure> VisitIt(Program node)
        {
            var assertLocations = new List<Procedure>();
            foreach (var impl in node.TopLevelDeclarations.OfType<Implementation>())
            {
                if (QKeyValueExtensions.FindBoolAttribute(impl.Attributes, "entrypoint"))
                    continue;
                if (cba.Util.BoogieVerify.ignoreAssertMethods.Contains(impl.Name))
                    continue;

                impl.Blocks.ForEach(block =>
                    block.Cmds.OfType<AssignCmd>()
                    .ForEach(cmd =>
                    {
                        foreach (var lhs in cmd.Lhss)
                            if (lhs.DeepAssignedVariable.Name == cba.Util.BoogieVerify.assertsPassed)
                                assertLocations.Add(impl.Proc);

                    }));
            }
            return assertLocations;
        }
    }

    /* builds the call-graph */
    public class BuildCallGraph : cba.Util.FixedVisitor
    {
        public BuildCallGraph()
        {
            graph = new CallGraph();
        }

        /* callgraph */
        public class CallGraph
        {
            public CallGraph()
            {
                callers = new Dictionary<Procedure, List<Procedure>>();
                callees = new Dictionary<Procedure, List<Procedure>>();
            }

            public Dictionary<Procedure, List<Procedure>> callers;
            public Dictionary<Procedure, List<Procedure>> callees;

            public void AddCallerCallee(Procedure caller, Procedure callee)
            {
                if (callers.All(x => x.Key.Name != callee.Name))//!callers.ContainsKey(callee))
                    callers.Add(callee, new List<Procedure>());

                if (callers[callee].All(x => x.Name != caller.Name))
                    callers[callee].Add(caller);

                if (callees.All(x => x.Key.Name != caller.Name))//!callees.ContainsKey(caller))
                    callees.Add(caller, new List<Procedure>());

                if (callees[caller].All(x => x.Name != callee.Name))
                    callees[caller].Add(callee);
            }

            public void PrintOut(System.IO.TextWriter output)
            {
                output.WriteLine("digraph G {");
                foreach (var pair in callers)
                    foreach (var second in pair.Value)
                        output.WriteLine("\"" + pair.Key.Name + "\"->\"" + second.Name + "\";");
                output.WriteLine("}");
            }
        }

        public CallGraph graph;
        protected Procedure currentProc;

        public override Implementation VisitImplementation(Implementation node)
        {
            currentProc = node.Proc;
            return base.VisitImplementation(node);
        }

        public override Cmd VisitCallCmd(CallCmd node)
        {
            graph.AddCallerCallee(currentProc, node.Proc);
            return base.VisitCallCmd(node);
        }
    }


    /****************************************
    * Class for statistical analysis        *
    ****************************************/

    public class Stats
    {
        public int numInlined = 0;
        public int vcSize = 0;
        public int bck = 0;
        public int stacksize = 0;
        public int calls = 0;
        public long time = 0;

        public void print()
        {
            Console.WriteLine("--------- Stats ---------");
            Console.WriteLine("number of functions inlined: " + numInlined);
            Console.WriteLine("number of backtracking: " + bck);
            Console.WriteLine("total number of assertions in Z3 stack: " + stacksize);
            Console.WriteLine("total number of Z3 calls: " + calls);
            Console.WriteLine("total time spent in Z3: (tick) " + time);
            Console.WriteLine("-------------------------");
        }
    }


    /****************************************
    *          Stratified Inlining          *
    ****************************************/

    /* stratified inlining technique */
    public class StratifiedInlining : StratifiedVC
    {
        public static readonly string ForceInlineAttr = "ForceInline";
        public static int StratifiedInliningVerbose = 0;
        public static int StackDepthBound = 0;

        public Stats stats;

        /* call-site to VC map -- used for trace construction */
        public Dictionary<StratifiedCallSite, StratifiedVC> attachedVC;
        public Dictionary<StratifiedVC, StratifiedCallSite> attachedVCInv;

        /* VC of main */
        private StratifiedVC svc;

        /*  Parent linking -- used only for computing the recursion depth */
        public Dictionary<StratifiedCallSite, StratifiedCallSite> parent;        

        // Set of implementations
        HashSet<string> implementations;

        /* results of the initial program analyses */
        private List<Procedure> assertMethods;
        private BuildCallGraph.CallGraph callGraph;

        /* main procedure (fake main) */
        private Procedure mainProc;

        /* Call Tree after VerifyImplementation */
        private HashSet<string> CallTree;

        /* An extra Boolean associated with each VC */
        private Dictionary<StratifiedVC, VCExpr> controlBoolean;

        /* extra Recursion bound */
        public Dictionary<string, int> extraRecBound;

        /* Procedures that hit the recursion bound */
        public HashSet<string> procsHitRecBound;

        private DI di;

        /* Forced inline procs */
        HashSet<string> forceInlineProcs;

        // verification start time
        DateTime startTime;

        public HashSet<string> GetCallTree()
        {
            return CallTree;
        }

        /* initial analyses */
        public void RunInitialAnalyses(Program prog)
        {
            LocateAsserts locate = new LocateAsserts();
            assertMethods = locate.VisitIt(prog);
            mainProc = prog.TopLevelDeclarations.OfType<Implementation>()
                .Where(impl => QKeyValueExtensions.FindBoolAttribute(impl.Attributes, "entrypoint"))
                .Select(impl => impl.Proc)
                .FirstOrDefault();

            Debug.Assert(mainProc != null);

            /* if no asserts in methods, we don't need fwd/bck, neither callgraph and the associated transformations */
            if (assertMethods.Count <= 0)
            {
                MacroSI.PRINT_DETAIL("No assert detected in the methods -- use foward approach instead.");
                return;
            }
            else
            {
                MacroSI.PRINT_DETAIL(assertMethods.Count + " methods containing asserts detected");
                if (StratifiedInliningVerbose > 1)
                    foreach (var method in assertMethods)
                        Console.WriteLine("-> " + method.Name);
            }

            BuildCallGraph builder = new BuildCallGraph();
            builder.Visit(prog);
            callGraph = builder.graph;

            if (StratifiedInliningVerbose > 3)
                callGraph.PrintOut(Console.Out);
        }

        /* depth in the call tree */
        public int StackDepth(StratifiedCallSite cs)
        {
            int i = 1;
            StratifiedCallSite iter = cs;
            while (parent.ContainsKey(iter))
            {
                iter = parent[iter]; /* previous callsite */
                i++;
            }
            return i;
        }

        /* depth of the recursion inlined so far */
        public int RecursionDepth(StratifiedCallSite cs)
        {
            int i = 1;
            StratifiedCallSite iter = cs;
            while (parent.ContainsKey(iter))
            {
                iter = parent[iter]; /* previous callsite */
                if (iter.callSite.calleeName == cs.callSite.calleeName)
                    i++; /* recursion */
            }
            return i;
        }

        /* Has this call-site reached the bound, given extraRecBound */
        public bool HasExceededRecursionDepth(StratifiedCallSite cs, int bound) {

            var i = RecursionDepth(cs);

            // Usual
            if (!extraRecBound.ContainsKey(cs.callSite.calleeName))
                return (i > bound);

            // Support extraRecBound
            return i > (bound + extraRecBound[cs.callSite.calleeName]);
        }

        /* for measuring Z3 stack */
        protected void Push()
        {
            stats.stacksize++;
            svc.info.vcgen.prover.Push();
        }

        /* for measuring Z3 stack */
        protected void Pop()
        {
            stats.stacksize--;
            svc.info.vcgen.prover.Pop();

        }

        struct SiState
        {
            public Dictionary<StratifiedCallSite, StratifiedVC> attachedVC;
            public Dictionary<StratifiedVC, StratifiedCallSite> attachedVCInv;
            public Dictionary<StratifiedCallSite, StratifiedCallSite> parent;
            public HashSet<StratifiedCallSite> openCallSites;
            public DI di;

            public static SiState SaveState(StratifiedInlining SI, HashSet<StratifiedCallSite> openCallSites)
            {
                var ret = new SiState();
                ret.attachedVC = new Dictionary<StratifiedCallSite, StratifiedVC>(SI.attachedVC);
                ret.attachedVCInv = new Dictionary<StratifiedVC, StratifiedCallSite>(SI.attachedVCInv);
                ret.parent = new Dictionary<StratifiedCallSite, StratifiedCallSite>(SI.parent);
                ret.openCallSites = new HashSet<StratifiedCallSite>(openCallSites);
                ret.di = SI.di.Copy();
                return ret;
            }

            public void ApplyState(StratifiedInlining SI, ref HashSet<StratifiedCallSite> openCallSites)
            {
                SI.attachedVC = attachedVC;
                SI.attachedVCInv = attachedVCInv;
                SI.parent = parent;
                SI.di = di;
                openCallSites = this.openCallSites;
            }
        }

        enum DecisionType { MUST_REACH, BLOCK };
        class Decision : Tuple<DecisionType, int, StratifiedCallSite>
        {
            public Decision(DecisionType dt, int num, StratifiedCallSite cs)
                : base(dt, num, cs) { }

            public DecisionType decisionType
            {
                get { return Item1; }
            }

            public int num
            {
                get { return Item2; }
            }

            public StratifiedCallSite cs
            {
                get { return Item3; }
            }
        }

        class TimeGraph 
        {
            Dictionary<int, string> Nodes;
            Dictionary<int, HashSet<Tuple<int, string, double>>> Edges;
            Stack<int> currNodeStack;
            DateTime startTime;
            static int dmpCnt = 0;

            public TimeGraph()
            {
                currNodeStack = new Stack<int>();
                Nodes = new Dictionary<int, string>();
                Edges = new Dictionary<int, HashSet<Tuple<int, string, double>>>();
                startTime = DateTime.Now;

                Nodes.Add(0, "main");
                Push(0);
            }

            public int Count()
            {
                return Nodes.Count;
            }


            private void AddEdge(int n1, int n2, string label1, double label2)
            {
                if(!Edges.ContainsKey(n1))
                    Edges.Add(n1, new HashSet<Tuple<int, string, double>>());
                Edges[n1].Add(Tuple.Create(n2, label1, label2));
            }

            public void ToDot()
            {
                using (var fs = new System.IO.StreamWriter("tg" + (dmpCnt++) + ".dot"))
                {
                    fs.WriteLine("digraph TG {");

                    foreach (var tup in Nodes)
                    {
                        fs.WriteLine("{0} [label=\"{1}\"]", tup.Key, tup.Value);
                    }

                    foreach (var tup in Edges)
                    {
                        foreach (var tgt in tup.Value)
                            fs.WriteLine("{0} -> {1} [label=\"{2} {3}\"]", tup.Key, tgt.Item1, tgt.Item2, tgt.Item3.ToString("F2"));
                    }
                        
                    fs.WriteLine("}");

                }
            }

            void Push(int node)
            {
                currNodeStack.Push(node);
            }

            public void Pop(int n)
            {
                while (n > 0) { n--; currNodeStack.Pop(); }
                startTime = DateTime.Now;
            }

            public void AddEdge(string tgt, string label)
            {
                var tgtnode = Nodes.Count;
                Nodes.Add(tgtnode, tgt);

                AddEdge(currNodeStack.Peek(), tgtnode, label, (DateTime.Now - startTime).TotalSeconds);
                Push(tgtnode);
                startTime = DateTime.Now;
            }

            public void AddEdgeDone(string label)
            {
                var tgtnode = Nodes.Count;
                Nodes.Add(tgtnode, "Done");

                AddEdge(currNodeStack.Peek(), tgtnode, label, (DateTime.Now - startTime).TotalSeconds);
                startTime = DateTime.Now;
            }

            public double ComputeTimes(int nthreads)
            {
                // First, construct the time graph properly with times on nodes (not edges)
                var nodeToTime = new Dictionary<int, double>();
                var nodeToChildren = new Dictionary<int, HashSet<int>>();

                // Nodes
                foreach (var tup in Edges)
                    foreach (var e in tup.Value)
                        nodeToTime.Add(e.Item1, e.Item3);

                nodeToTime.Keys.ForEach(n => nodeToChildren.Add(n, new HashSet<int>()));

                // Edges
                foreach (var tup in Edges)
                    foreach (var e in tup.Value)
                    {
                        var n1 = tup.Key;
                        var n2 = e.Item1;
                        if (!nodeToTime.ContainsKey(n1) || !nodeToTime.ContainsKey(n2))
                            continue;
                        nodeToChildren[n1].Add(n2);
                    }

                var rand = new Random((int)DateTime.Now.Ticks);

                var root = Edges[0].First().Item1;
                var isZero = new Func<double, bool>(d => d < 0.00001);
                var isNull = new Func<Tuple<int, double>, bool>(t => t.Item1 < 0);

                var threads = new Tuple<int, double>[nthreads];
                for (int i = 0; i < nthreads; i++)
                    threads[i] = Tuple.Create(-1, 0.0);

                var totaltime = 0.0;
                var available = new List<int>();
                available.Add(root);

                while (true)
                {
                    // Allocate to idle threads
                    for (int i = 0; i < nthreads; i++)
                    {
                        if (!isNull(threads[i])) continue;
                        if (!available.Any()) continue;
                        var index = rand.Next(available.Count);
                        threads[i] = Tuple.Create(available[index], nodeToTime[available[index]]);
                        available.RemoveAt(index);
                    }
                    if (threads.All(t => isNull(t))) break;

                    // Run
                    var min = threads.Where(t => !isNull(t)).Min(t => t.Item2);
                    totaltime += min;
                    for (int i = 0; i < nthreads; i++)
                    {
                        if (isNull(threads[i])) continue;
                        var tleft = threads[i].Item2 - min;
                        if (isZero(tleft))
                        {
                            nodeToChildren[threads[i].Item1].ForEach(n => available.Add(n));
                            threads[i] = Tuple.Create(-1, 0.0);
                        }
                        else
                            threads[i] = Tuple.Create(threads[i].Item1, tleft);
                    }
                }

                return totaltime;
            }
        }

        // Assert that we must reach this VC; returns the list of call sites asserted
        public List<Tuple<StratifiedVC, Block>> AssertMustReach(StratifiedVC svc, HashSet<Tuple<StratifiedVC, Block>> prevAsserted)
        {
            var ret = new List<Tuple<StratifiedVC, Block>>();

            // This is most likely redundant
            svc.info.vcgen.prover.Assert(svc.MustReach(svc.info.Implementation.Blocks[0], null /* TODO: add ControlFlowIdMap parameter */), true);

            if (!attachedVCInv.ContainsKey(svc))
                return ret;

            var iter = attachedVCInv[svc]; 
            while (parent.ContainsKey(iter))
            {
                var vc = attachedVC[parent[iter]];
                var callblock = vc.callSites.First(tup => tup.Value.Contains(iter)).Key;
                
                var key = Tuple.Create(vc, callblock);
                if (prevAsserted != null && !prevAsserted.Contains(key))
                {
                    svc.info.vcgen.prover.Assert(vc.MustReach(callblock, null /* TODO: add ControlFlowIdMap parameter */), true);
                    ret.Add(key);
                }
                iter = parent[iter];
            }
            svc.info.vcgen.prover.Assert(svc.MustReach(svc.callSites.First(tup => tup.Value.Contains(iter, null /* TODO: add ControlFlowIdMap parameter */)).Key), true);
            return ret;
        }

        void MustNotFail(StratifiedCallSite scs, StratifiedVC svc)
        {
            if (!svc.info.interfaceExprVars.Exists(x => x.Name.Contains(cba.Util.BoogieVerify.assertsPassed)))
                return;

            var index = svc.info.interfaceExprVars.FindLastIndex(x => x.Name.Contains(cba.Util.BoogieVerify.assertsPassed));
            VCExpr assertsPass = null;
            if (cba.Util.BoogieVerify.assertsPassedIsInt)
            {
                Microsoft.BaseTypes.BigNum zero = Microsoft.BaseTypes.BigNum.FromInt(0);
                assertsPass = svc.info.vcgen.prover.VCExprGen.Eq(scs.interfaceExprs[index], svc.info.vcgen.prover.VCExprGen.Integer(zero));
            }
            else
                assertsPass = scs.interfaceExprs[index];

            svc.info.vcgen.prover.Assert(svc.info.vcgen.prover.VCExprGen.Implies(scs.callSiteExpr, assertsPass), true);
        }

        // TODO: add this to BoogieVerifyOptions
        static string prevMain = null;
        static DagOracle prevDag = null;

        static int dumpCnt = 0;

        private void Merge(StratifiedCallSite scs, StratifiedVC svc)
        {
            MacroSI.PRINT_DEBUG("    ~ attaching to existing callsite ");
            svc.info.vcgen.prover.LogComment("Attaching for " + scs.callSite.calleeName);
            var toassert = AttachByEquality(scs, svc);
            var cb = GetControlBoolean(svc);
            toassert = svc.info.vcgen.prover.VCExprGen.Implies(scs.callSiteExpr, svc.info.vcgen.prover.VCExprGen.And(cb, toassert));

            di.Merged(scs, svc);
            stats.vcSize += SizeComputingVisitor.ComputeSize(toassert);

            svc.info.vcgen.prover.Assert(toassert, true);
            attachedVC[scs] = svc;
        }

        // Return the control Boolean for the VC
        private VCExpr GetControlBoolean(StratifiedVC vc)
        {
            if (controlBoolean.ContainsKey(vc))
                return controlBoolean[vc];
            var lit = svc.info.vcgen.prover.VCExprGen.Variable("extraControlBoolSIDI" + controlBoolean.Count,
                Microsoft.Boogie.Type.Bool);
            controlBoolean.Add(vc, lit);
            return lit;
        }

        // Return unique call ID of a call site
        private int GetSiCallId(StratifiedCallSite scs)
        {
            return QKeyValue.FindIntAttribute(scs.callSite.Attributes, "si_unique_call", -1);
        }

        // Get persistent ID of a callsite
        private string GetPersistentID(StratifiedCallSite scs)
        {
            if (!parent.ContainsKey(scs))
                return string.Format("{0}_131_{1}", scs.callSite.calleeName, GetSiCallId(scs));

            var ret = GetPersistentID(parent[scs]);
            return string.Format("{0}_262_{1}_393_{2}", ret, scs.callSite.calleeName, GetSiCallId(scs));
        }

        // Get persistent ID of a VC
        private string GetPersistentID(StratifiedVC vc)
        {
            var ret = "";
            if (attachedVCInv.ContainsKey(vc))
            {
                var scs = attachedVCInv[vc];
                ret = GetPersistentID(scs);
            }
            return string.Format("{0}_262_{1}", ret, vc.info.Implementation.Name);
        }

        // 'Attach' inlined from Boogie/StratifiedVC.cs (and made static)
        // TODO: add it to Boogie/StratifiedVC.cs
        // ---------------------------------------- 
        // Original Attach works with interface variables renaming. We don't want this, as we backtrack sometimes.
        // We add an equality clause instead.
        public static VCExpr AttachByEquality(StratifiedCallSite callee, StratifiedVC svcCallee)
        {
            System.Diagnostics.Contracts.Contract.Assert(callee.callSite.interfaceExprs.Count == svcCallee.interfaceExprVars.Count);
            StratifiedInliningInfo info = svcCallee.info;
            ProverInterface prover = info.vcgen.prover;
            VCExpressionGenerator gen = prover.VCExprGen;

            VCExpr conjunction = VCExpressionGenerator.True;

            for (int i = 0; i < svcCallee.interfaceExprVars.Count; i++)
            {
                /* interface variables */
                VCExpr equality = gen.Eq(svcCallee.interfaceExprVars[i], callee.interfaceExprs[i]);
                conjunction = gen.And(equality, conjunction);
            }

            return conjunction;
        }

        private static void Partition<T>(HashSet<T> values, out HashSet<T> part1, out HashSet<T> part2)
        {
            part1 = new HashSet<T>();
            part2 = new HashSet<T>();
            var size = values.Count;
            var crossed = false;
            var curr = 0;
            foreach (var s in values)
            {
                if (crossed) part2.Add(s);
                else part1.Add(s);
                curr++;
                if (!crossed && curr >= size / 2) crossed = true;
            }
        }
    }

    class BijectiveDictionary<T1, T2> : IEnumerable<KeyValuePair<T1, T2>>, IEnumerable
    {
        Dictionary<T1, T2> map1;
        Dictionary<T2, T1> map2;

        public BijectiveDictionary()
        {
            map1 = new Dictionary<T1, T2>();
            map2 = new Dictionary<T2, T1>();
        }

        public void Add(T1 elem1, T2 elem2)
        {
            map1.Add(elem1, elem2);
            map2.Add(elem2, elem1);
        }

        public T2 this[T1 key]
        {
            get
            {
                return map1[key];
            }
        }

        public T1 this[T2 key]
        {
            get
            {
                return map2[key];
            }
        }

        public T2 GetRange(T1 key)
        {
            return map1[key];
        }

        public T1 GetDomain(T2 key)
        {
            return map2[key];
        }

        public IEnumerable<T1> GetDomain()
        {
            return map1.Keys;
        }

        public IEnumerable<T2> GetRange()
        {
            return map2.Keys;
        }

        public bool ContainsDomain(T1 key)
        {
            return map1.ContainsKey(key);
        }

        public bool ContainsRange(T2 key)
        {
            return map2.ContainsKey(key);
        }

        public IEnumerator GetEnumerator()
        {
            return map1.GetEnumerator();
        }

        IEnumerator<KeyValuePair<T1, T2>> IEnumerable<KeyValuePair<T1, T2>>.GetEnumerator()
        {
            return map1.GetEnumerator();
        }
    }

    public enum MERGING_STRATEGY { NONE, FIRST, RANDOM_PICK, RANDOM, MAXC, OPT };

    class DI
    {    
        MERGING_STRATEGY strategy;

        public bool disabled { get; private set; }
        public TimeSpan timeTaken { get; private set; }

        StratifiedInlining SI;

        Dictionary<StratifiedCallSite, StratifiedVC> containingVC;
        Dictionary<StratifiedVC, int[]> vcToRecVector;

        ProgramDisjointness Disj;
        IndexComputer IndexC;

        // For Merging (computed once)
        static DagOracle optimalDag = null;

        DagOracle currentDag;
        BijectiveDictionary<StratifiedVC, DagOracle.DagNode> vcNodeMap;
        BijectiveDictionary<DagOracle.DagNode, DagOracle.DagNode> currentOptNodeMapping;

        Random random;

        private DI()
        { }

        public DI(StratifiedInlining SI, bool disabled)
        {
            this.SI = SI;
            timeTaken = TimeSpan.Zero;
            var st = DateTime.Now;

            containingVC = new Dictionary<StratifiedCallSite, StratifiedVC>();
            vcToRecVector = new Dictionary<StratifiedVC, int[]>();
            this.disabled = disabled;
            random = new Random((int)DateTime.Now.Ticks);

            IndexC = null;
            Disj = null;
            currentDag = new DagOracle(SI.info.vcgen.program, null);
            vcNodeMap = new BijectiveDictionary<StratifiedVC, DagOracle.DagNode>();
            currentOptNodeMapping = new BijectiveDictionary<DagOracle.DagNode, DagOracle.DagNode>();

            if (!disabled)
            {
                IndexC = new IndexComputer(SI.info.vcgen.program);
                var impls = new Dictionary<string, Implementation>();
                SI.info.implName2StratifiedInliningInfo.ForEach(tup => impls.Add(tup.Key, tup.Value.impl));
                Disj = new ProgramDisjointness(impls);

                currentDag = new DagOracle(SI.info.vcgen.program, Disj, SI.extraRecBound);

                strategy = PickStrategy();
                
                if (strategy == MERGING_STRATEGY.OPT && optimalDag == null)
                {
                    optimalDag = new DagOracle(SI.info.vcgen.program, Disj, SI.extraRecBound);
                    var tsize = optimalDag.ConstructCallDagOnTheFly(true, strategy);
                    Console.WriteLine("Constructed optimal dag, with {0} nodes (max {1})", optimalDag.ComputeSize(), tsize);
                }

            }
            timeTaken += (DateTime.Now - st);
        }

        public DI Copy()
        {
            var ret = new DI();
            ret.SI = SI;
            ret.disabled = disabled;
            ret.Disj = Disj;
            ret.strategy = strategy;
            ret.timeTaken = TimeSpan.Zero;
            ret.containingVC = new Dictionary<StratifiedCallSite, StratifiedVC>(containingVC);
            ret.vcToRecVector = new Dictionary<StratifiedVC, int[]>(vcToRecVector);
            ret.IndexC = IndexC;
            ret.currentDag = currentDag.Copy();
            
            ret.vcNodeMap = new BijectiveDictionary<StratifiedVC, DagOracle.DagNode>();
            ret.currentOptNodeMapping = new BijectiveDictionary<DagOracle.DagNode, DagOracle.DagNode>();
            foreach (var n in vcNodeMap.GetDomain())
                ret.vcNodeMap.Add(n, vcNodeMap[n]);
            foreach (var n in currentOptNodeMapping.GetDomain())
                ret.currentOptNodeMapping.Add(n, currentOptNodeMapping.GetRange(n));

            ret.random = new Random((int)DateTime.Now.Ticks);

            return ret;
        }

        public static MERGING_STRATEGY PickStrategy()
        {
            var strategy = MERGING_STRATEGY.FIRST;
            if (BoogieVerify.Options.extraFlags.Contains("DiNone"))
            {
                Console.WriteLine("Selecting DAG Inilining strategy: None");
                strategy = MERGING_STRATEGY.NONE;
            }
            if (BoogieVerify.Options.extraFlags.Contains("DiRandom"))
            {
                Console.WriteLine("Selecting DAG Inilining strategy: Random");
                strategy = MERGING_STRATEGY.RANDOM;
            }
            if (BoogieVerify.Options.extraFlags.Contains("DiRandomPick"))
            {
                Console.WriteLine("Selecting DAG Inilining strategy: RandomPick");
                strategy = MERGING_STRATEGY.RANDOM_PICK;
            }
            if (BoogieVerify.Options.extraFlags.Contains("DiMaxc"))
            {
                Console.WriteLine("Selecting DAG Inilining strategy: maxc");
                strategy = MERGING_STRATEGY.MAXC;
            }
            if (BoogieVerify.Options.extraFlags.Contains("DiOpt"))
            {
                Console.WriteLine("Selecting DAG Inilining strategy: static opt");
                strategy = MERGING_STRATEGY.OPT;
            }
            return strategy;
        }

        public DagOracle GetDag()
        {
            return currentDag;
        }

        public int ComputeSize()
        {
            return currentDag.ComputeSize();
        }

        public HashSet<StratifiedVC> DisjointNodes(StratifiedVC vc)
        {
            var ret = new HashSet<StratifiedVC>();
            var disj = currentDag.AllDisjointNodes();
            disj[vcNodeMap[vc]].ForEach(n => ret.Add(vcNodeMap[n]));
            return ret;
        }

        // Return the number of disjoint nodes for each node
        public Dictionary<StratifiedVC, int> ComputeNumDisjoint()
        {
            var ret = new Dictionary<StratifiedVC, int>();
            var disj = currentDag.AllDisjointNodes();
            foreach (var tup in disj)
                ret.Add(vcNodeMap[tup.Key], tup.Value.Count);
            return ret;
        }

        // Return subtree sizes for each node
        public Dictionary<StratifiedVC, HashSet<StratifiedVC>> ComputeSubtrees()
        {
            var ret = new Dictionary<StratifiedVC, HashSet<StratifiedVC>>();
            Dictionary<DagOracle.DagNode, int> nodeToTreeSize;
            Dictionary<DagOracle.DagNode, HashSet<DagOracle.DagNode>> nodeToChildren;
            currentDag.ComputeDagSizes(out nodeToTreeSize, out nodeToChildren);

            nodeToChildren.ForEach(tup => ret.Add(vcNodeMap[tup.Key],
                new HashSet<StratifiedVC>(tup.Value.Select(n => vcNodeMap[n]))));

            return ret;
        }

        public void DeleteNode(StratifiedVC vc)
        {
            Debug.Assert(vcNodeMap.ContainsDomain(vc));
            var node = vcNodeMap[vc];
            if(currentDag.Nodes.Contains(node))
                currentDag.DeleteNodeAndDecendants(node);
        }

        public bool VcExists(StratifiedVC vc)
        {
            if (!vcNodeMap.ContainsDomain(vc))
                return false;
            return currentDag.Nodes.Contains(vcNodeMap[vc]);
        }

        public void CheckSanity()
        {
            var st = DateTime.Now;
            if(currentDag.Nodes.Count != 0)
                currentDag.CheckSanity();
            timeTaken += (DateTime.Now - st);
        }

        public void RegisterMain(StratifiedVC vc)
        {
            var st = DateTime.Now;

            RegisterVC(vc);

            if (disabled) return;

            Debug.Assert(currentDag.Nodes.Count == 0);

            var rv = IndexC.GetMainRv();
            var index = IndexC.GetIndex(vc.info.Implementation.Name, rv);
            vcToRecVector.Add(vc, rv);

            // Add to dag
            var node = new DagOracle.DagNode(index, vc.info.Implementation.Name, 1);

            vcNodeMap.Add(vc, node);
            currentDag.AddNode(node);

            currentDag.SetRoot(node);
            if (optimalDag != null)
                currentOptNodeMapping.Add(node, optimalDag.GetRoot());

            timeTaken += (DateTime.Now - st);
        }

        void RegisterVC(StratifiedVC vc)
        {
            foreach (var cs in vc.CallSites)
                containingVC[cs] = vc;           
        }

        public void Expanded(StratifiedCallSite cs, StratifiedVC vc)
        {
            var st = DateTime.Now;
            RegisterVC(vc);

            if (disabled) return;
            Debug.Assert(cs.callSite.calleeName == vc.info.Implementation.Name);

            var n1 = vcNodeMap[containingVC[cs]];

            int[] rv2 = null;
            var id2 = GetTargetId(cs, out rv2);
            vcToRecVector.Add(vc, rv2);

            // create node
            var n2 = new DagOracle.DagNode(id2, vc.info.Implementation.Name, 1);

            vcNodeMap.Add(vc, n2);
            currentDag.AddNode(n2);

            // Add edge to our dag
            var e = QKeyValue.FindIntAttribute(cs.callSite.Attributes, "si_unique_call", -1);
            currentDag.AddEdge(new DagOracle.DagEdge(n1, n2, e));

            if (optimalDag != null && !currentOptNodeMapping.ContainsDomain(n2))
            {
                var o1 = currentOptNodeMapping.GetRange(n1);
                var o2 = optimalDag.FindSuccessor(o1, e, n2.ImplName);
                if (o2 == null)
                {
                    Console.WriteLine("Unable to find successor of {0} and {1} to {2}", o1.id, e, n2.ImplName);
                    Debug.Assert(false);
                }
                currentOptNodeMapping.Add(n2, o2);
            }

            timeTaken += (DateTime.Now - st);
        }

        public void Merged(StratifiedCallSite cs, StratifiedVC vc)
        {
            var st = DateTime.Now;
            if (disabled) return;

            var n1 = vcNodeMap[containingVC[cs]];
            var n2 = vcNodeMap[vc];
            var e = QKeyValue.FindIntAttribute(cs.callSite.Attributes, "si_unique_call", -1);
            currentDag.AddEdge(new DagOracle.DagEdge(n1, n2, e));

            //currentDag.CheckSanity();

            timeTaken += (DateTime.Now - st);
        }

        string GetTargetId(StratifiedCallSite cs, out int[] rv2)
        {
            var n1 = vcNodeMap[containingVC[cs]];
            var rv1 = vcToRecVector[containingVC[cs]];
            rv2 = IndexC.IncrementIndex(cs.callSite.calleeName, rv1);
            var id2 = IndexC.GetIndex(cs.callSite.calleeName, rv2);

            return id2;
        }

        public StratifiedVC FindMergeCandidate(StratifiedCallSite cs)
        {
            var st = DateTime.Now;
            var ret = FindMergeCandidateInternal(cs);
            timeTaken += (DateTime.Now - st);
            return ret;
        }

        StratifiedVC FindMergeCandidateInternal(StratifiedCallSite cs)
        {
            if (disabled) return null;
            if (strategy == MERGING_STRATEGY.NONE) return null;

            Debug.Assert(!SI.attachedVC.ContainsKey(cs));

            var e = QKeyValue.FindIntAttribute(cs.callSite.Attributes, "si_unique_call", -1);
            int[] rv = null;
            var candidates = currentDag.FindMergeCandidates(vcNodeMap[containingVC[cs]], e, GetTargetId(cs, out rv));

            if (strategy == MERGING_STRATEGY.FIRST)
            {
                var n = candidates.FirstOrDefault();
                if (n == null) return null;
                return vcNodeMap[n];
            }

            var matches = candidates.ToList();
            if (matches.Count == 0) return null;

            if (strategy == MERGING_STRATEGY.MAXC)
            {
                var max = 0.0;
                StratifiedVC maxc = null;
                foreach (var c in matches)
                {
                    var size = currentDag.Descendants(c).Count / (1 + currentDag.Ancestors(c).Count);
                    if (max < size)
                    {
                        max = size;
                        maxc = vcNodeMap[c];
                    }
                }
                return maxc;
            }

            if (strategy == MERGING_STRATEGY.RANDOM)
            {
                var choice = random.Next(0, matches.Count + 2);
                if (StratifiedInlining.StratifiedInliningVerbose > 0)
                    Console.WriteLine("Making choice {0} of {1} for {2}", choice, matches.Count - 1, cs.callSite.calleeName);
                if (choice >= matches.Count) return null;
                return vcNodeMap[matches[choice]];
            }

            if (strategy == MERGING_STRATEGY.RANDOM_PICK)
            {
                var choice = random.Next(0, matches.Count);
                if (StratifiedInlining.StratifiedInliningVerbose > 0)
                    Console.WriteLine("Making choice {0} of {1} for {2}", choice, matches.Count - 1, cs.callSite.calleeName);
                return vcNodeMap[matches[choice]];
            }

            Debug.Assert(strategy == MERGING_STRATEGY.OPT);
            Debug.Assert(optimalDag != null);
            // this is where we are
            var n1 = vcNodeMap[containingVC[cs]];
            var call = QKeyValue.FindIntAttribute(cs.callSite.Attributes, "si_unique_call", -1);
            var o1 = currentOptNodeMapping.GetRange(n1);
            var o2 = optimalDag.FindSuccessor(o1, call, cs.callSite.calleeName);
            Debug.Assert(o2 != null);

            // lets see if our current dag has o2
            if (currentOptNodeMapping.ContainsRange(o2))
            {
                var n2 = currentOptNodeMapping.GetDomain(o2);
                Debug.Assert(matches.Contains(n2));
                return vcNodeMap[n2];
            }
            else
            {
                // Lets not merge right now
                return null;
            }

        }

        public void Dump(string filename)
        {
            currentDag.Dump(filename);
            ComputeDagSizes();
        }

        // Return the sizes of shared dags; and more info about the largest shared sub-tree
        private void ComputeDagSizes()
        {
            if(!disabled)
                currentDag.ComputeDagSizes();
        }

    }

    class IndexComputer
    {
        Program program;
        // call graph
        Graph<string> cg;
        // scc graph
        Graph<SCC<string>> sccgraph;
        // proc to reachable procs
        Dictionary<string, HashSet<string>> procToReachableProcs;
        // proc to index
        Dictionary<string, int> procToIndex;
        // index to proc
        string[] indexToProc;
        // recursive procs
        HashSet<string> recursiveProcs;

        public IndexComputer(Program program)
        {
            this.program = program;

            // call graph
            cg = BoogieUtil.GetCallGraph(program);

            // SCCs 
            var sccs = new StronglyConnectedComponents<string>(cg.Nodes,
                s => cg.Predecessors(s), s => cg.Successors(s));
            sccs.Compute();

            var procToScc = new Dictionary<string, SCC<string>>();

            foreach (var scc in sccs)
                foreach (var p in scc)
                    procToScc.Add(p, scc);

            // graph over SCCs
            sccgraph = new Graph<SCC<string>>();
            foreach (var scc in sccs)
                sccgraph.AddSource(scc);
            foreach (var edge in cg.Edges)
            {
                var s1 = procToScc[edge.Item1];
                var s2 = procToScc[edge.Item2];
                if (s1 != s2)
                    sccgraph.AddEdge(s2, s1);
            }

            // top sort SCC dag
            var sortedscc = sccgraph.TopologicalSort();

            var sccToReachableScc = new Dictionary<SCC<string>, HashSet<SCC<string>>>();
            foreach (var scc in sortedscc)
            {
                var r = new HashSet<SCC<string>>();
                r.Add(scc);
                foreach (var s in sccgraph.Predecessors(scc))
                    r.UnionWith(sccToReachableScc[s]);
                sccToReachableScc.Add(scc, r);
            }

            // Get recursive procs reachable from proc
            procToReachableProcs = new Dictionary<string, HashSet<string>>();
            foreach (var p in cg.Nodes)
            {
                procToReachableProcs[p] = new HashSet<string>();
                sccToReachableScc[procToScc[p]].ForEach(scc => procToReachableProcs[p].UnionWith(scc));
            }

            recursiveProcs = BoogieUtil.GetCyclicNodes<string>(cg);

            indexToProc = new string[cg.Nodes.Count];
            procToIndex = new Dictionary<string, int>();
            int i = 0;
            cg.Nodes.ForEach(p => { indexToProc[i] = p; procToIndex[p] = i; i++; });
        }

        public int[] GetMainRv()
        {
            var rv = new int[indexToProc.Length];
            for (int i = 0; i < rv.Length; i++) rv[i] = 0;
            return rv;
        }

        public int[] IncrementIndex(string proc, int[] recursionVector)
        {
            var ret = new int[recursionVector.Length];
            Array.Copy(recursionVector, ret, ret.Length);
            ret[procToIndex[proc]]++;
            return ret;
        }

        public string GetIndex(string proc, int[] recursionVector)
        {
            Debug.Assert(recursionVector.Length == indexToProc.Length);
            var procs = new HashSet<string>(recursiveProcs);
            procs.IntersectWith(procToReachableProcs[proc]);

            var ret = "";
            for (int i = 0; i < recursionVector.Length; i++)
            {
                if (!procs.Contains(indexToProc[i])) continue;
                ret += recursionVector[i].ToString();
            }
            return proc + "[" + ret + "]";
        }
    }

    public class ProgramDisjointness
    {
        Dictionary<string, Implementation> impls;

        // cache: impl -> pairs of disjoint calls
        Dictionary<string, HashSet<Tuple<int, int>>> exclusiveCache;

        public ProgramDisjointness(Program program)
        {
            var map = new Dictionary<string, Implementation>();
            program.TopLevelDeclarations.OfType<Implementation>()
                .ForEach(impl => map.Add(impl.Name, impl));

            exclusiveCache = new Dictionary<string, HashSet<Tuple<int, int>>>();
            this.impls = new Dictionary<string, Implementation>(map);
        }

        public ProgramDisjointness(Dictionary<string, Implementation> impls)
        {
            exclusiveCache = new Dictionary<string, HashSet<Tuple<int, int>>>();
            this.impls = new Dictionary<string, Implementation>(impls);
        }

        public bool IsExclusive(string impl, int n1, int n2)
        {
            return IsExclusive(impls[impl], n1, n2);
        }

        public bool IsExclusive(Implementation impl, int n1, int n2)
        {
            if (n1 < 0 || n2 < 0)
                return false;

            if (exclusiveCache.ContainsKey(impl.Name))
                return !exclusiveCache[impl.Name].Contains(Tuple.Create(n1, n2)) &&
                    !exclusiveCache[impl.Name].Contains(Tuple.Create(n2, n1));

            var blockToCalls = new Dictionary<Block, HashSet<int>>();
            var seen = new HashSet<int>();
            foreach (var b in impl.Blocks)
            {
                blockToCalls.Add(b, new HashSet<int>());
                foreach (var cmd in b.Cmds)
                {
                    // check for both passified program as well as non-passified
                    QKeyValue attr = null;
                    if (cmd is AssumeCmd && (cmd as AssumeCmd).Expr is NAryExpr &&
                        impls.ContainsKey(((cmd as AssumeCmd).Expr as NAryExpr).Fun.FunctionName))
                    {
                        attr = (cmd as AssumeCmd).Attributes;
                    }
                    else if (cmd is CallCmd && impls.ContainsKey((cmd as CallCmd).callee))
                    {
                        attr = (cmd as CallCmd).Attributes;
                    }
                    if (attr == null) continue;
                    var v = QKeyValue.FindIntAttribute(attr, "si_unique_call", -1);
                    if (v < 0) continue;
                    blockToCalls[b].Add(v);

                    // sanity check
                    if (seen.Contains(v))
                    {
                        Console.WriteLine("WARNING: Duplicate si_unique_call annotations in {0}", impl.Name);
                        exclusiveCache.Add(impl.Name, new HashSet<Tuple<int, int>>());
                        return false;
                    }
                    seen.Add(v);
                }
            }

            var graph = Program.GraphFromImpl(impl);
            var canReachMe = new Dictionary<Block, HashSet<Block>>();
            impl.Blocks.ForEach(b => canReachMe.Add(b, new HashSet<Block>()));

            foreach (var b in graph.TopologicalSort())
            {
                canReachMe[b].Add(b);
                foreach (var p in graph.Predecessors(b))
                    canReachMe[b].UnionWith(canReachMe[p]);
            }

            var reachable = new HashSet<Tuple<int, int>>();
            foreach (var b in impl.Blocks)
            {
                var from = new HashSet<int>();
                canReachMe[b].ForEach(p => from.UnionWith(blockToCalls[p]));
                foreach (var tgt in blockToCalls[b])
                {
                    from.ForEach(src => reachable.Add(Tuple.Create(src, tgt)));
                }
            }

            exclusiveCache.Add(impl.Name, reachable);
            return !exclusiveCache[impl.Name].Contains(Tuple.Create(n1, n2)) &&
                !exclusiveCache[impl.Name].Contains(Tuple.Create(n2, n1));
        }

        public void DumpCFG(Implementation impl, string filename)
        {
            var graph = Program.GraphFromImpl(impl);
            var str = new System.IO.StreamWriter(filename);
            str.WriteLine("digraph DAG {");

            graph.Nodes
                .ForEach(n => str.WriteLine("{0} [ label = \"{1}\" color=black shape=box];", n.UniqueId, n.Label));

            foreach (var edge in graph.Edges)
                str.WriteLine("{0} -> {1} [ label = \"{2}\"];", edge.Item1.UniqueId, edge.Item2.UniqueId, "");

            str.WriteLine("}");
            str.Close();
        }

    }

    public class DagOracle
    {
        public class DagNode
        {
            public string ImplName;
            public string id;
            public int Size;
            public int uid { get; private set; }
            static int uidCounter = 0;

            public DagNode(string id, string ImplName, int Size)
            {
                this.id = id;
                this.ImplName = ImplName;
                this.Size = Size;
                this.uid = uidCounter++;
            }

            public override string ToString()
            {
                return ImplName;
            }
        }

        public class DagEdge
        {
            public DagNode Source, Target;
            public int CallSite;

            public DagEdge(DagNode source, DagNode target, int callsite)
            {
                this.Source = source;
                this.Target = target;
                this.CallSite = callsite;
            }
        }

        Program program;
        Dictionary<string, int> extraRecBound;

        DagNode Root;
        public HashSet<DagNode> Nodes { get; private set; }
        public HashSet<DagEdge> Edges { get; private set; }
        ProgramDisjointness Disj;

        // Dependent information
        public Dictionary<DagNode, HashSet<DagEdge>> Children { get; private set; }
        public Dictionary<DagNode, HashSet<DagEdge>> Parents { get; private set; }
        Dictionary<string, HashSet<DagNode>> IdToNodes;

        // lazily extending optimial dag
        Action<string> lazyExtendDag;
        Graph<string> idgraph;
        Dictionary<string, string> idToProc;

        // For stats
        TimeSpan tmpTime1; //, tmpTime2;

        public DagOracle(Program program, Dictionary<string, int> extraRecBound)
            :this(program, new ProgramDisjointness(program), extraRecBound)
        {
        }

        public DagOracle(Program program, ProgramDisjointness disj, Dictionary<string, int> extraRecBound)
        {
            Nodes = new HashSet<DagNode>();
            Edges = new HashSet<DagEdge>();
            Children = new Dictionary<DagNode, HashSet<DagEdge>>();
            Parents = new Dictionary<DagNode, HashSet<DagEdge>>();
            IdToNodes = new Dictionary<string, HashSet<DagNode>>();
            Root = null;

            this.Disj = disj;
            this.program = program;
            this.extraRecBound = extraRecBound;
        }

        // Create a fresh copy of the Dag
        public DagOracle Copy()
        {
            var ret = new DagOracle(program, Disj, extraRecBound);
            foreach (var n in Nodes)
                ret.AddNode(n);
            foreach (var e in Edges)
                ret.AddEdge(e);
            ret.Root = Root;

            return ret;
        }

        public void SetRoot(DagNode node)
        {
            AddNode(node);
            Root = node;
        }

        public DagNode GetRoot()
        {
            return Root;
        }

        IEnumerable<DagEdge> OutGoing(DagNode node)
        {
            return Children[node];
        }

        IEnumerable<DagEdge> InComing(DagNode node)
        {
            Debug.Assert(Nodes.Contains(node));

            return Parents[node];
        }

        public int ComputeSize()
        {
            RemoveUnreachableNodes();

            var ret = 0;
            Nodes.ForEach(node => ret += node.Size);
            return ret;
        }

        public IEnumerable<DagNode> FindMergeCandidates(DagNode n1, int cs, string targetId)
        {
            if (!IdToNodes.ContainsKey(targetId) || IdToNodes[targetId].Count == 0)
                yield break;

            var an = Ancestors(n1);
            
            foreach (var n2 in IdToNodes[targetId])
            {
                Debug.Assert(!an.Contains(n2));

                // check ancestors of n1
                if (!CheckDisjointness(n2, an, new HashSet<DagNode>()))
                    continue;

                var d2 = Descendants(n2);

                var suitable = true;
                foreach (var e in Children[n1])
                {
                    if (Disj.IsExclusive(n1.ImplName, e.CallSite, cs)) continue;
                    var d1 = Descendants(e.Target);
                    if (d1.Intersection(d2).Count != 0)
                    {
                        suitable = false;
                        break;
                    }
                }
                if (!suitable) continue;
                
                // For each decendant of n2, if we go up, when it hits an,
                // then disjointness should hold; this is the entire check and above
                // are just filters
                foreach (var dn in d2)
                {
                    if (!CheckDisjointness(dn, an, d2))
                    {
                        suitable = false;
                        break;
                    }
                }

                if (!suitable) continue;

                yield return n2;
            }
            yield break;
        }

        // Return the set of all nodes disjoint with n. The second argument is optional; used for optimization
        // Precondition: This only works correctly when the DAG is a tree
        public Dictionary<DagNode, HashSet<DagNode>> AllDisjointNodes()
        {
            Dictionary<DagNode, int> nodeToTreeSize;
            Dictionary<DagNode, HashSet<DagNode>> nodeToChildren;
            ComputeDagSizes(out nodeToTreeSize, out nodeToChildren);

            var ret = new Dictionary<DagNode, HashSet<DagNode>>();
            Nodes.ForEach(n => ret.Add(n, new HashSet<DagNode>()));
            AllDisjointNodesHelper(Root, ret, nodeToChildren);
            return ret;
        }

        void AllDisjointNodesHelper(DagNode n, Dictionary<DagNode, HashSet<DagNode>> nodeToDisj, Dictionary<DagNode, HashSet<DagNode>> nodeToDescendants)
        {
            foreach (var c in Children[n].Select(e => e.Target))
            {
                nodeToDisj[c].UnionWith(nodeToDisj[n]);
            }

            foreach (var e1 in Children[n])
            {
                foreach (var e2 in Children[n])
                {
                    if (e1 == e2) continue;
                    if (!Disj.IsExclusive(n.ImplName, e1.CallSite, e2.CallSite)) continue;
                    nodeToDisj[e1.Target].UnionWith(nodeToDescendants[e2.Target]);
                }
            }

            foreach (var c in Children[n].Select(e => e.Target))
            {
                AllDisjointNodesHelper(c, nodeToDisj, nodeToDescendants);
            }

        }


        public bool IsDisjoint(DagNode n1, DagNode n2)
        {
            if (n1 == n2) return false;
            if (Ancestors(n1).Contains(n2)) return false;

            // Light up ancestors of n2
            var ancestors = Ancestors(n2);
            Debug.Assert(!ancestors.Contains(n1));

            // Walk up from n1 and check
            return CheckDisjointness(n1, ancestors, new HashSet<DagNode>());
        }

        private bool CheckDisjointness(DagNode n, HashSet<DagNode> ancestors, HashSet<DagNode> blocked)
        {
            Debug.Assert(!ancestors.Contains(n));
            if(!Parents.ContainsKey(n)) return true;
            
            foreach (var pedge in Parents[n])
            {
                if (blocked.Contains(pedge.Source)) continue;

                if (ancestors.Contains(pedge.Source))
                {
                    foreach (var e in Children[pedge.Source].Where(c => ancestors.Contains(c.Target)))
                    {
                        if (!Disj.IsExclusive(pedge.Source.ImplName, pedge.CallSite, e.CallSite))
                            return false;
                    }
                }
                else
                {
                    if (!CheckDisjointness(pedge.Source, ancestors, blocked))
                        return false;
                }
            }
            return true;
        }

        private void Merge(DagNode n1, DagNode n2)
        {
            // Swing parents to n1
            var todelete = new List<DagEdge>();
            foreach (var edge in InComing(n2))
            {
                var nedge = new DagEdge(edge.Source, n1, edge.CallSite);
                todelete.Add(edge);
                AddEdge(nedge);
            }

            // delete n2
            todelete.ForEach(DeleteEdge);
            DeleteNodeAndDecendants(n2);
        }

        // constructs a DAG over IDs (procedures + recursion vector)
        Graph<string> ConstructIdDag(out string main, out Dictionary<string, string> idToProc)
        {
            var ret = new Graph<string>();
            idToProc = new Dictionary<string, string>();
            
            var impls = new Dictionary<string, Implementation>();
            program.TopLevelDeclarations.OfType<Implementation>()
                .ForEach(impl => impls.Add(impl.Name, impl));

            var ep = program.TopLevelDeclarations.OfType<Implementation>()
                .Where(impl => QKeyValueExtensions.FindBoolAttribute(impl.Attributes, "entrypoint"))
                .FirstOrDefault();
            main = ep.Name;

            var impl2index = new Dictionary<string, int>();
            impls.ForEach(tup => impl2index.Add(tup.Key, impl2index.Count));

            var cg = BoogieUtil.GetCallGraph(program);
            var recursiveProcs = BoogieUtil.GetCyclicNodes<string>(cg);

            var procToReachableRecProcs = new Dictionary<string, HashSet<string>>();
            var ImplToId = new Func<Implementation, int[], string>((impl, rv) =>
            {
                var str = "";
                if (!procToReachableRecProcs.ContainsKey(impl.Name))
                {
                    procToReachableRecProcs.Add(impl.Name,
                        recursiveProcs.Intersection(BoogieUtil.GetReachableNodes<string>(impl.Name, cg)));
                }
                foreach (var r in procToReachableRecProcs[impl.Name])
                    str += rv[impl2index[r]].ToString();
                var id = string.Format("{0}[{1}]", impl.Name, str);
                
                return id;
            });


            var recursionVector = new int[impls.Count];
            for (int i = 0; i < recursionVector.Length; i++)
                recursionVector[i] = 0;

            var root = ImplToId(ep, recursionVector);
            idToProc[root] = ep.Name;

            ret.AddSource(root);

            var frontier = new Stack<Tuple<string, string, int[]>>();

            frontier.Push(Tuple.Create(root, ep.Name, recursionVector));

            while (frontier.Any())
            {
                var tt = frontier.Peek();
                frontier.Pop();

                var id = tt.Item1;
                var implName = tt.Item2;
                var rv = tt.Item3;

                foreach (var succImpl in cg.Successors(implName))
                {
                    var rvcopy = new int[rv.Length];
                    Array.Copy(rv, rvcopy, rv.Length);

                    rvcopy[impl2index[succImpl]]++;

                    if (HasExceededRecBound(succImpl, rvcopy[impl2index[succImpl]]))
                        continue;                    

                    var sid = ImplToId(impls[succImpl], rvcopy);
                    idToProc[sid] = succImpl;

                    ret.AddEdge(id, sid);
                    frontier.Push(Tuple.Create(sid, succImpl, rvcopy));
                }
            }
            return ret;
        }

        bool HasExceededRecBound(string impl, int bound)
        {
            if (!extraRecBound.ContainsKey(impl))
                return (bound > 999 /* TODO: CommandLineOptions.RecursionBound removed in Boogie 3.5.5 */);
            return bound > 999 /* TODO: CommandLineOptions.RecursionBound removed in Boogie 3.5.5 */ + extraRecBound[impl];
        }

        // Returns the size of the fully expanded tree
        public int ConstructCallDagOnTheFly(bool lazy, MERGING_STRATEGY strategy)
        {
            if (StratifiedInlining.StratifiedInliningVerbose > 0)
                Console.WriteLine("Constructing the call dag on the fly");

            var main = "";
            idToProc = null;
            idgraph = ConstructIdDag(out main, out idToProc);
            var sorted = idgraph.TopologicalSort();
            Debug.Assert(sorted.Count() != 0);
            var rootid = sorted.First();

            // id -> #nodes with that id in the fully expanded tree 
            // (used for debugging)
            var id2numnodes = new Dictionary<string, int>();
            idgraph.Nodes.ForEach(s => id2numnodes.Add(s, 0));
            id2numnodes[rootid] = 1;

            // Start with empty call dag
            Root = new DagNode(rootid, main, 1);
            AddNode(Root);

            var impls = new Dictionary<string, Implementation>();
            program.TopLevelDeclarations.OfType<Implementation>()
                .ForEach(impl => impls.Add(impl.Name, impl));

            // impl to its calls
            var implToCalls = new Dictionary<string, HashSet<Tuple<int, string>>>();
            foreach (var tup in impls)
            {
                implToCalls.Add(tup.Key, new HashSet<Tuple<int, string>>());
                foreach (var block in tup.Value.Blocks)
                {
                    foreach (var cmd in block.Cmds.OfType<CallCmd>())
                    {
                        if (!impls.ContainsKey(cmd.callee))
                            continue;
                        var cs = QKeyValue.FindIntAttribute(cmd.Attributes, "si_unique_call", -1);
                        implToCalls[tup.Key].Add(Tuple.Create(cs, cmd.callee));
                    }
                }
            }

            if (StratifiedInlining.StratifiedInliningVerbose > 0)
                Console.WriteLine("ID graph done, and top sorted (size = {0})", idgraph.Nodes.Count);

            if (strategy != MERGING_STRATEGY.OPT)
            {
                var NodeToCalls = new Func<DagNode, List<Tuple<DagNode, int, string>>>(n =>
                    {
                        var r = new List<Tuple<DagNode, int, string>>();
                        implToCalls[n.ImplName].ForEach(t => r.Add(Tuple.Create(n, t.Item1, t.Item2)));
                        return r;
                    });

                var opencalls = new List<Tuple<DagNode, int, string>>();
                opencalls.AddRange(NodeToCalls(Root));
                var rand = new Random((int)DateTime.Now.Ticks);
                while (opencalls.Count != 0)
                {
                    var next = rand.Next(0, opencalls.Count);
                    var cs = opencalls[next];
                    opencalls.RemoveAt(next);
                    var targetid = idgraph.Successors(cs.Item1.id).Where(id => idToProc[id] == cs.Item3).FirstOrDefault();
                    if (targetid == null) continue; // hit rec. bound

                    var candidates = FindMergeCandidates(cs.Item1, cs.Item2, targetid);

                    if (strategy == MERGING_STRATEGY.FIRST)
                    {
                        var t = candidates.FirstOrDefault();
                        if (t == null)
                        {
                            t = new DagNode(targetid, cs.Item3, 1);
                            opencalls.AddRange(NodeToCalls(t));
                        }
                        AddEdge(new DagEdge(cs.Item1, t, cs.Item2));
                        continue;
                    }

                    var candidatesList = candidates.ToList();

                    if (candidatesList.Count == 0)
                    {
                        var t = new DagNode(targetid, cs.Item3, 1);
                        opencalls.AddRange(NodeToCalls(t));
                        AddEdge(new DagEdge(cs.Item1, t, cs.Item2));
                        continue;
                    }

                    if (strategy == MERGING_STRATEGY.RANDOM)
                    {
                        
                        var choice = rand.Next(0, candidatesList.Count + 2);
                        DagNode t = null;
                        if (choice > candidatesList.Count - 1)
                        {
                            t = new DagNode(targetid, cs.Item3, 1);
                            opencalls.AddRange(NodeToCalls(t));
                        }
                        else
                        {
                            t = candidatesList[choice];
                        }
                        AddEdge(new DagEdge(cs.Item1, t, cs.Item2));
                        continue;
                    }

                    if (strategy == MERGING_STRATEGY.RANDOM_PICK)
                    {
                        var choice = rand.Next(0, candidatesList.Count);
                        var t = candidatesList[choice];
                        AddEdge(new DagEdge(cs.Item1, t, cs.Item2));
                        continue;
                    }

                    if (strategy == MERGING_STRATEGY.MAXC)
                    {
                        var max = 0.0;
                        DagNode t = null;
                        foreach (var c in candidatesList)
                        {
                            var size = Descendants(c).Count / (1 + Ancestors(c).Count);
                            if (max <= size)
                            {
                                max = size;
                                t = c;
                            }
                        }
                        AddEdge(new DagEdge(cs.Item1, t, cs.Item2));
                        continue;
                    }
                }
                return 0;
            }
            else
            {

                var idsExtended = new HashSet<string> { rootid };

                lazyExtendDag = new Action<string>(id =>
                    {
                        foreach (var n in sorted)
                        {
                            if (idsExtended.Contains(n)) continue;
                            idsExtended.Add(n);
                            ExtendAndCompress(n, idgraph, idToProc, implToCalls, id2numnodes);
                            if (n == id) break;
                        }
                    });

                if (lazy)
                    return 0;

                lazyExtendDag(sorted.Last());
            }

            /*
            foreach (var id in sorted)
            {
                if (id == rootid) continue;
                ExtendAndCompress(id, idgraph, idToProc, implToCalls, id2numnodes);
            }
            */            

            var ret = 0;
            id2numnodes.ForEach(tup => ret += tup.Value);
            return ret;
        }

        public void ExtendDag(string id)
        {
            Debug.Assert(lazyExtendDag != null);
            lazyExtendDag(id);
        }

        void ExtendAndCompress(string id, Graph<string> idgraph, 
            Dictionary<string, string> idToProc,
            Dictionary<string, HashSet<Tuple<int, string>>> implToCalls,
            Dictionary<string, int> id2numnodes)
        {
            if(StratifiedInlining.StratifiedInliningVerbose > 0)
                Console.WriteLine("Adding id {0}", id);
            var predids = idgraph.Predecessors(id);
            Debug.Assert(predids.Count() != 0);

            // Add the edges to the new id
            foreach (var pred in predids)
            {
                var predproc = idToProc[pred];
                var succproc = idToProc[id];
                var calls = new HashSet<int>(
                    implToCalls[predproc].Where(t => t.Item2 == succproc).Select(t => t.Item1));

                // compute number of nodes
                id2numnodes[id] += id2numnodes[pred] * calls.Count;

                foreach (var n in IdToNodes[pred])
                    GenerateSuccessors(n, id, succproc, calls);
            }

            // compress
            Compress(id);
        }

        void GenerateSuccessors(DagNode node, string targetid, string targetproc, HashSet<int> calls)
        {
            foreach (var call in calls)
            {
                AddEdge(new DagEdge(node, new DagNode(targetid, targetproc, 1), call));
            }
        }

        void Compress(string id)
        {
            if(IdToNodes.ContainsKey(id))
                IdToNodes[id].RemoveWhere(n => !Nodes.Contains(n));

            if (!IdToNodes.ContainsKey(id) ||
                IdToNodes[id].Count() == 1)
                return;

            // induced subgraph on all dag nodes with name "name"
            Microsoft.Boogie.GraphUtil.Graph<DagNode> graph = null;
            Dictionary<DagNode, HashSet<DagNode>> adj = null;

            var st = DateTime.Now;

            if (IdToNodes[id].Count < 100)
            {
                graph = new Microsoft.Boogie.GraphUtil.Graph<DagNode>();

                // Make sure all the nodes are inserted
                IdToNodes[id].ForEach(n => graph.AddSource(n));

                foreach (var n1 in IdToNodes[id])
                {
                    foreach (var n2 in IdToNodes[id])
                    {
                        if (n1.uid <= n2.uid) continue;

                        if (!IsDisjoint(n1, n2))
                        {
                            graph.AddEdge(n1, n2);
                            graph.AddEdge(n2, n1);
                        }
                    }
                }
                //System.IO.File.WriteAllText("induced.dot", graph.ToDot(n => n.uid.ToString()));
            }
            else
            {
                // Gather the subset of the dag that we should look at
                var ancestors = new HashSet<DagNode>();
                IdToNodes[id].ForEach(v => ancestors.UnionWith(Ancestors(v)));

                HashSet<DagNode> tt = null;
                GetAdjacency(Root, id, out adj, out tt, ancestors);
            }

            #region Debugging code for adjacency code
            /*
            foreach (var n in graph.Nodes)
            {
                var s1 = new HashSet<DagNode>(graph.Successors(n));
                var s2 = adj[n];
                if (!s1.SetEquals(s2))
                {
                    var ancestors = new HashSet<DagNode>();
                    IdToNodes[id].ForEach(v => ancestors.UnionWith(Ancestors(v)));
                    Dump("err.dot", ancestors);
                    Debug.Assert(false);
                }
            }
            */
            #endregion

            tmpTime1 += (DateTime.Now - st);

            var coloring = graph != null ? ColorGraph<DagNode>(graph) : ColorGraph<DagNode>(IdToNodes[id], n => adj[n]);

            // Got the coloring!
            if (StratifiedInlining.StratifiedInliningVerbose > 0)
                Console.WriteLine("Got a coloring of {0} nodes with {1} colors", IdToNodes[id].Count, coloring.Values.Max() + 1);

            // pick representation in each color
            var representative = new Dictionary<int, DagNode>();
            foreach (var tup in coloring)
            {
                if (!representative.ContainsKey(tup.Value))
                    representative.Add(tup.Value, tup.Key);
            }

            // Merge
            foreach (var n in (new HashSet<DagNode>(IdToNodes[id])))
            {
                var r = representative[coloring[n]];
                if (r == n) continue;
                //Console.WriteLine("Merging for proc {0}, {1} with {2}", n.ImplName, n.uid, r.uid);
                Merge(r, n);
            }

            //if(merged)
            //    RemoveUnreachableNodes();
            // Done!
        }

        void GetAdjacency(DagNode node, string id, out Dictionary<DagNode, HashSet<DagNode>> adj, out HashSet<DagNode> reachable,
            HashSet<DagNode> universe)
        {
            adj = new Dictionary<DagNode, HashSet<DagNode>>();
            reachable = new HashSet<DagNode>();

            if (node.id == id)
            {
                adj.Add(node, new HashSet<DagNode>());
                reachable.Add(node);
                return;
            }

            if (!universe.Contains(node))
                return;

            var childToDescendants = new Dictionary<DagEdge, HashSet<DagNode>>();
            foreach (var e in Children[node])
            {
                Dictionary<DagNode, HashSet<DagNode>> a;
                HashSet<DagNode> d;
                GetAdjacency(e.Target, id, out a, out d, universe);

                // pt. wise union of adj
                foreach (var tup in a)
                {
                    if (!adj.ContainsKey(tup.Key))
                        adj.Add(tup.Key, new HashSet<DagNode>());
                    adj[tup.Key].UnionWith(tup.Value);
                }

                // stash decendants
                childToDescendants[e] = d;
            }

            // decide fate of node pairs whose least common ancestor is "node"
            foreach (var e1 in Children[node])
            {
                reachable.UnionWith(childToDescendants[e1]);
                foreach (var e2 in Children[node])
                {
                    if (e1 == e2) continue;
                    
                    if (Disj.IsExclusive(node.ImplName, e1.CallSite, e2.CallSite)) continue;
                    var g1 = childToDescendants[e1].Difference(childToDescendants[e2]);
                    var g2 = childToDescendants[e2].Difference(childToDescendants[e1]);

                    g1.RemoveWhere(a => a.id != id);
                    g2.RemoveWhere(a => a.id != id);

                    foreach(var a in g1)
                        adj[a].UnionWith(g2);

                    foreach (var a in g2)
                        adj[a].UnionWith(g1);                        
                }
            }

        }

        Dictionary<Node, int> ColorGraph<Node>(Microsoft.Boogie.GraphUtil.Graph<Node> graph)
        {
            return ColorGraph(graph.Nodes, n =>new HashSet<Node>(graph.Successors(n)));
        }

        // Colors a graph
        Dictionary<Node, int> ColorGraph<Node>(HashSet<Node> nodes, Func<Node, HashSet<Node>> Adjacency)
        {
            var nodelist = new List<Node>(nodes);
            var rand = new Random(0); //(int)DateTime.Now.Ticks);
            // number of node orderings to try
            int numTries = 10;

            var maxColors = Int32.MaxValue;
            Dictionary<Node, int> finalColoring = null;

            while (numTries > 0)
            {
                numTries--;
                // generate random ordering
                var perm = RandomPermutation(nodelist, rand);
                int maxc;
                var colors = Color(Adjacency, perm, out maxc);
                if (maxc < maxColors)
                {
                    finalColoring = colors;
                    maxColors = maxc;
                }
            }

            return finalColoring;
        }

        List<Node> RandomPermutation<Node>(List<Node> nodes, Random rand)
        {
            var ls = new List<Node>(nodes);
            var pm = new int[ls.Count];
            RandomPermutation(pm, rand);

            for (int i = 0; i < pm.Length; i++)
            {
                ls[i] = nodes[pm[i]];
            }

            return ls;
        }

        void RandomPermutation(int[] Permutation, Random rand)
        {
            int i;
            for (i = 0; i < Permutation.Length; i++)
            {
                var j = rand.Next(i + 1);
                Permutation[i] = Permutation[j];
                Permutation[j] = i;
            }
        }

        // returns a coloring of the nodes, given an ordering
        private Dictionary<Node, int> Color<Node>(Func<Node, HashSet<Node>> Adj,
            IEnumerable<Node> orderedNodes, out int maxColor)
        {
            var color = new Dictionary<Node, int>();
            maxColor = 0;
            foreach (var n in orderedNodes)
            {
                var neighborColors = new HashSet<int>();
                var consider = new HashSet<Node>(color.Keys);
                consider.IntersectWith(Adj(n));

                consider
                    .ForEach(s => neighborColors.Add(color[s]));

                // find the least c that is not in neightColors
                var c = 0;
                while (true)
                {
                    if (!neighborColors.Contains(c))
                    {
                        break;
                    }
                    c++;
                }
                maxColor = Math.Max(maxColor, c);
                color.Add(n, c);
            }
            return color;
        }


        public HashSet<DagNode> Ancestors(DagNode node)
        {
            var ret = new HashSet<DagNode>();
            ret.Add(node);

            var frontier = new HashSet<DagNode>();
            frontier.Add(node);

            while (frontier.Count != 0)
            {
                var next = new HashSet<DagNode>();
                foreach (var p in frontier.Where(s => Parents.ContainsKey(s)))
                    next.UnionWith(Parents[p].Select(e => e.Source));

                frontier = next;
                frontier.ExceptWith(ret);

                ret.UnionWith(next);
            }
            return ret;
        }

        public HashSet<DagNode> Descendants(DagNode node)
        {
            var ret = new HashSet<DagNode>();
            ret.Add(node);

            var frontier = new HashSet<DagNode>();
            frontier.Add(node);

            while (frontier.Count != 0)
            {
                var next = new HashSet<DagNode>();
                foreach (var v in frontier)
                    next.UnionWith(Children[v].Select(e => e.Target));

                frontier = next;
                frontier.ExceptWith(ret);

                ret.UnionWith(next);
            }
            return ret;
        }

        public void AddNode(DagNode node)
        {
            if (Nodes.Contains(node))
                return;
            Nodes.Add(node);
            
            IdToNodes.InitAndAdd(node.id, node);

            Children.Add(node, new HashSet<DagEdge>());
            Parents.Add(node, new HashSet<DagEdge>());
        }

        public void AddEdge(DagEdge edge)
        {
            //Console.WriteLine("Adding edge {0} to {1}", edge.Source.id, edge.Target.id);
            Edges.Add(edge);
            AddNode(edge.Source);
            AddNode(edge.Target);

            Children[edge.Source].Add(edge);
            Parents[edge.Target].Add(edge);
        }

        public void DeleteEdge(DagEdge edge)
        {
            Edges.Remove(edge);
            Children[edge.Source].Remove(edge);
            Parents[edge.Target].Remove(edge);
        }

        public void DeleteNode(DagNode node)
        {
            Debug.Assert(Root != node);
            Debug.Assert(Nodes.Contains(node));

            var edges = new HashSet<DagEdge>();
            edges.UnionWith(Children[node]);
            edges.UnionWith(Parents[node]);
            foreach(var e in edges)
                DeleteEdge(e);

            Nodes.Remove(node);
            Children.Remove(node);
            Parents.Remove(node);
            IdToNodes[node.id].Remove(node);
        }

        public DagNode FindSuccessor(DagNode source, int call, string target)
        {
            if (lazyExtendDag != null)
            {
                Debug.Assert(idgraph != null);
                var succid = idgraph.Successors(source.id).Where(id => idToProc[id] == target)
                    .First();
                lazyExtendDag(succid);
            }

            return Children[source].Where(e => e.CallSite == call && e.Target.ImplName == target)
                .Select(e => e.Target).FirstOrDefault();
        }

        public void DeleteNodeAndDecendants(DagNode node)
        {
            Decendants(node).ForEach(DeleteNode);
        }

        public static DagOracle ConstructCallDag(Program program, Dictionary<string, int> extraRecBound)
        {
            var ret = new DagOracle(program, extraRecBound);

            var impls = new Dictionary<string, Implementation>();
            program.TopLevelDeclarations.OfType<Implementation>()
                .ForEach(impl => impls.Add(impl.Name, impl));

            var ep = program.TopLevelDeclarations.OfType<Implementation>()
                .Where(impl => QKeyValueExtensions.FindBoolAttribute(impl.Attributes, "entrypoint"))
                .FirstOrDefault();

            var implToCalls = new Dictionary<string, HashSet<Tuple<int, string>>>();
            foreach (var tup in impls)
            {
                implToCalls.Add(tup.Key, new HashSet<Tuple<int, string>>());
                foreach (var block in tup.Value.Blocks)
                {
                    foreach (var cmd in block.Cmds.OfType<CallCmd>())
                    {
                        if (!impls.ContainsKey(cmd.callee))
                            continue;
                        var cs = QKeyValue.FindIntAttribute(cmd.Attributes, "si_unique_call", -1);
                        implToCalls[tup.Key].Add(Tuple.Create(cs, cmd.callee));
                    }
                }
            }

            var impl2index = new Dictionary<string, int>();
            impls.ForEach(tup => impl2index.Add(tup.Key, impl2index.Count));

            var cg = BoogieUtil.GetCallGraph(program);
            var recursiveProcs = BoogieUtil.GetCyclicNodes<string>(cg);

            var procToReachableRecProcs = new Dictionary<string, HashSet<string>>();
            var ImplToNode = new Func<Implementation, int[], DagNode>((impl, rv) =>
            {
                var size = 1;
                var str = "";
                if (!procToReachableRecProcs.ContainsKey(impl.Name))
                {
                    procToReachableRecProcs.Add(impl.Name,
                        recursiveProcs.Intersection(BoogieUtil.GetReachableNodes<string>(impl.Name, cg)));
                }
                foreach (var r in procToReachableRecProcs[impl.Name])
                    str += rv[impl2index[r]].ToString();
                return new DagNode(string.Format("{0}[{1}]", impl.Name, str), impl.Name, size);
            });


            var recursionVector = new int[impls.Count];
            for (int i = 0; i < recursionVector.Length; i++)
                recursionVector[i] = 0;

            var root = ImplToNode(ep, recursionVector);
            var frontier = new Stack<Tuple<DagNode, int[]>>();
            
            frontier.Push(Tuple.Create(root, recursionVector));

            while (frontier.Any())
            {
                var tt = frontier.Peek();
                frontier.Pop();

                var n = tt.Item1;
                var rv = tt.Item2;

                foreach (var tup in implToCalls[n.ImplName])
                {
                    var rvcopy = new int[rv.Length];
                    Array.Copy(rv, rvcopy, rv.Length);

                    rvcopy[impl2index[tup.Item2]]++;

                    if (ret.HasExceededRecBound(tup.Item2, rvcopy[impl2index[tup.Item2]]))
                        continue;

                    var s = ImplToNode(impls[tup.Item2], rvcopy);
                    ret.AddEdge(new DagEdge(n, s, tup.Item1));
                    frontier.Push(Tuple.Create(s, rvcopy));
                }                
            }

            ret.SetRoot(root);

            return ret;
        }

        public void Compress()
        {
            var graph = new Microsoft.Boogie.GraphUtil.Graph<string>();

            foreach (var e in Edges)
                graph.AddEdge(e.Source.id, e.Target.id);

            graph.AddSource(Root.id);

            tmpTime1 = TimeSpan.Zero;

            // Top-sort
            var sorted = graph.TopologicalSort();

            var compressed = new HashSet<string>();
            foreach (var n in sorted)
            {
                if (compressed.Contains(n))
                    continue;
                compressed.Add(n);

                Console.WriteLine("Compressing {0}", n);
                Compress(n);
                //CheckSanity();
            }
            Console.WriteLine("tmpTim1: {0}", tmpTime1.TotalSeconds.ToString("F2"));
        }

        void ColorTreeNode(DagNode node, Dictionary<string, int> MinColorAvailable, IEnumerable<string> ids, Dictionary<DagNode, int> FinalColoring)
        {
            FinalColoring[node] = MinColorAvailable[node.id];
            MinColorAvailable[node.id]++;

            if (Children[node].Count == 0)
                return;

            // First, let us color the out-going edges of n
            var graph = new Microsoft.Boogie.GraphUtil.Graph<DagNode>();
            Children[node].ForEach(e => graph.AddSource(e.Target));

            foreach (var e1 in Children[node])
            {
                foreach (var e2 in Children[node])
                {
                    if (e1 == e2) continue;
                    if (!IsDisjoint(e1.Target, e2.Target))
                        graph.AddEdge(e1.Target, e2.Target);
                }
            }
            // color this graph
            var coloring = ColorGraph<DagNode>(graph);

            var maxcolor = coloring.Values.Max();

            // construct inverse map for the coloring
            var colorToNodes = new Dictionary<int, HashSet<DagNode>>();
            for (int i = 0; i <= maxcolor; i++)
                colorToNodes.Add(i, new HashSet<DagNode>());
            coloring.ForEach(tup => colorToNodes[tup.Value].Add(tup.Key));

            // Node to its mincolor mapping
            var nodeToMinColorAvailable = new Dictionary<DagNode, Dictionary<string, int>>();

            // iterate over the colors in ascending order
            for (int i = 0; i <= maxcolor; i++)
            {
                foreach (var n in colorToNodes[i])
                {
                    var map = new Dictionary<string, int>(MinColorAvailable);

                    // take max over its neighbors that have a smaller color
                    foreach (var s in graph.Successors(n))
                    {
                        if (coloring[s] > i) continue;
                        foreach (var id in ids)
                            map[id] = Math.Max(map[id], nodeToMinColorAvailable[s][id]);
                    }

                    // Recurse
                    ColorTreeNode(n, map, ids, FinalColoring);
                    nodeToMinColorAvailable[n] = map;
                }
            }

        }

        public void CheckSanity()
        {
            // Check that all mergings are safe
            foreach (var node in Nodes.Where(n => Parents[n].Count > 1))
            {
                if (!CheckSanityForward(node))
                {
                    Dump("err.dot", Ancestors(node));
                    Console.WriteLine("DAG Sanity check failed!!");
                    Debug.Assert(false);
                }
            }

            HashSet<DagNode> tt = null; // temporary
            if(!CheckSanityBackward(Root, out tt)) {
                Console.WriteLine("DAG Sanity check failed!!");
                Debug.Assert(false);
            }

        }

        bool CheckSanityBackward(DagNode node, out HashSet<DagNode> reachable)
        {
            reachable = new HashSet<DagNode>{node};
            var childToDescendants = new Dictionary<DagEdge, HashSet<DagNode>>();
            foreach (var e in Children[node])
            {
                HashSet<DagNode> d;
                if (!CheckSanityBackward(e.Target, out d))
                    return false;
                childToDescendants[e] = d;
            }
            foreach (var e1 in Children[node])
            {
                reachable.UnionWith(childToDescendants[e1]);
                foreach (var e2 in Children[node])
                {
                    if (e1 == e2) continue;
                    if (childToDescendants[e1].Intersection(childToDescendants[e2]).Count > 0)
                    {
                        if (!Disj.IsExclusive(node.ImplName, e1.CallSite, e2.CallSite))
                            return false;
                    }
                }
            }

            return true;
        }
        
        bool CheckSanityForward(DagNode node)
        {
            foreach (var e1 in Parents[node])
            {
                foreach (var e2 in Parents[node])
                {
                    if (e1 == e2) continue;
                    if (e1.Source == e2.Source)
                    {
                        if (!Disj.IsExclusive(node.ImplName, e1.CallSite, e2.CallSite))
                        {
                            Console.WriteLine("Failed check 1: {0} {1} {2}", node.ImplName, e1.CallSite, e2.CallSite);
                            return false;
                        }
                        continue;
                    }
                    var a1 = Ancestors(e1.Source);
                    var a2 = Ancestors(e2.Source);

                    if (a1.Contains(e2.Source))
                    {
                        foreach (var e3 in Children[e2.Source])
                        {
                            if (e3 == e2) continue;
                            if (!a1.Contains(e3.Target)) continue;
                            if (!Disj.IsExclusive(e2.Source.ImplName, e2.CallSite, e3.CallSite))
                            {
                                Console.WriteLine("Failed check 2: {0} {1} {2} {3}", node.ImplName, e1.CallSite, e2.CallSite, e3.CallSite);
                                return false;
                            }
                        }
                        continue;
                    }

                    if (a2.Contains(e1.Source))
                    {
                        foreach (var e3 in Children[e1.Source])
                        {
                            if (e3 == e1) continue;
                            if (!a2.Contains(e3.Target)) continue;
                            if (!Disj.IsExclusive(e1.Source.ImplName, e1.CallSite, e3.CallSite))
                            {
                                Console.WriteLine("Failed check 3: {0} {1} {2} {3}", node.ImplName, e1.CallSite, e2.CallSite, e3.CallSite);
                                return false;
                            }
                        }

                        continue;
                    }

                    if (!IsDisjoint(e1.Source, e2.Source))
                    {
                        Console.WriteLine("Failed check 4: {0} {1} {2}", node.ImplName, e1.CallSite, e2.CallSite);
                        return false;
                    }
                }
            }
            return true;

        }

        void RemoveUnreachableNodes()
        {
            Debug.Assert(Root != null);

            var reached = Decendants(Root);

            var delete = new HashSet<DagNode>(Nodes);
            delete.ExceptWith(reached);
            delete.ForEach(DeleteNode);
        }

        HashSet<DagNode> Decendants(DagNode node)
        {
            var reached = new HashSet<DagNode> { node };
            var frontier = new HashSet<DagNode> { node };
            while (frontier.Any())
            {
                var next = new HashSet<DagNode>();
                frontier.ForEach(n =>
                    Children[n].ForEach(e => next.Add(e.Target)));
                next.ExceptWith(reached);
                frontier = next;
                reached.UnionWith(next);
            }
            return reached;
        }

        public void Dump(string filename)
        {
            if (Nodes.Count == 0 || Root == null)
                return;
            Dump(filename, Nodes);
            //Disj.DumpCFG(BoogieUtil.findProcedureImpl(program.TopLevelDeclarations, "main"), "main.dot");
        }

        public void Dump(string filename, HashSet<DagNode> nodes)
        {
            RemoveUnreachableNodes();

            var str = new System.IO.StreamWriter(filename);
            str.WriteLine("digraph DAG {");

            nodes
                .ForEach(n => str.WriteLine("{0} [ label = \"{1}\" color=black shape=box];", n.uid, n.ImplName));

            foreach (var edge in Edges.Where(e => nodes.Contains(e.Source) && nodes.Contains(e.Target)))
                str.WriteLine("{0} -> {1} [ label = \"{2}\"];", edge.Source.uid, edge.Target.uid, edge.CallSite);

            str.WriteLine("}");
            str.Close();
        }

        // Return the sizes of shared dags; and more info about the largest shared sub-tree
        public void ComputeDagSizes(out Dictionary<DagNode, int> nodeToTreeSizeMap,
            out Dictionary<DagNode, HashSet<DagNode>> nodeToChildrenMap)
        {
            var graph = new Microsoft.Boogie.GraphUtil.Graph<DagNode>();

            foreach (var e in Edges)
                graph.AddEdge(e.Target, e.Source);

            graph.AddSource(Root);

            // Top-sort
            var sorted = graph.TopologicalSort();
            var nodeToTreeSize = new Dictionary<DagNode, int>();
            var nodeToChildren = new Dictionary<DagNode, HashSet<DagNode>>();

            Nodes.ForEach(vc => nodeToTreeSize.Add(vc, 0));
            Nodes.ForEach(vc => nodeToChildren.Add(vc, new HashSet<DagNode>()));

            foreach (var n in sorted)
            {
                foreach (var s in Children[n].Select(e => e.Target))
                {
                    nodeToTreeSize[n] += nodeToTreeSize[s];
                    nodeToChildren[n].UnionWith(nodeToChildren[s]);
                }
                nodeToTreeSize[n]++;
                nodeToChildren[n].Add(n);
            }

            nodeToChildrenMap = nodeToChildren;
            nodeToTreeSizeMap = nodeToTreeSize;
        }

        // Return the sizes of shared dags; and more info about the largest shared sub-tree
        public int ComputeDagSizes()
        {
            Dictionary<DagNode, int> nodeToTreeSize;
            Dictionary<DagNode, HashSet<DagNode>> nodeToChildren;
            ComputeDagSizes(out nodeToTreeSize, out nodeToChildren);

            var hist = new Dictionary<int, int>(); // size -> count
            var largestsize = 0;
            DagNode largestnode = null;

            foreach (var n in Nodes)
            {
                if (Parents[n].Count > 1)
                {
                    var size = nodeToChildren[n].Count;
                    if (!hist.ContainsKey(size))
                        hist[size] = 0;
                    hist[size]++;

                    if (size > largestsize)
                    {
                        largestsize = size;
                        largestnode = n;
                    }
                }
            }
            
            if (largestnode != null)
            {
                Console.WriteLine("Shared node size distribution");
                hist.ForEach(tup => Console.Write("{0}: {1}  ", tup.Key, tup.Value));
                Console.WriteLine();

                Console.WriteLine("Largest shared subtree has size {0}, tree size {1}, for proc {2}", largestsize,
                    nodeToTreeSize[largestnode], largestnode.ImplName);

                Dump("largest.dot", Ancestors(largestnode));
            }
            Console.WriteLine("Tree size: {0}", nodeToTreeSize[Root]);
             
            return nodeToTreeSize[Root];
        }

    }
    
    /****************************************
    *      Counter-example Generation       *
    ****************************************/

    public class InsufficientDetailsToConstructCexPath : Exception
    {
        public InsufficientDetailsToConstructCexPath(string msg) : base(msg) { }

    }

    public class StratifiedInliningErrorReporter : ProverInterface.ErrorHandler
    {
        StratifiedInlining si;
        public VerifierCallback callback;
        StratifiedVC svc;
        public static TimeSpan ttime = TimeSpan.Zero;

        public bool reportTrace;
        public bool reportTraceIfNothingToExpand;

        public List<StratifiedCallSite> callSitesToExpand;
        List<Tuple<int, int>> orderedStateIds;

        public CommandLineOptions Options;

        public StratifiedInliningErrorReporter(VerifierCallback callback, StratifiedInlining si, StratifiedVC svc) : base(null)
        {
            this.callback = callback;
            this.si = si;
            this.svc = svc;
            this.reportTrace = false;
            this.reportTraceIfNothingToExpand = false;
        }

        public override int StartingProcId()
        {
            return svc.id;
        }

        private Absy Label2Absy(string procName, string label)
        {
            int id = int.Parse(label);
            var l2a = si.info.vcgen.implName2StratifiedInliningInfo[procName].label2absy;
            return (Absy)l2a[id];
        }

        public override void OnProverError(string message)
        {
            // Panic, shutdown!
            Console.WriteLine("Corral encountered a prover error. Giving up.");
            Console.Out.Flush();

            // Give a few seconds to the prover to shutdown
            var t1 =
            System.Threading.Tasks.Task.Run(async () =>
            {
                await System.Threading.Tasks.Task.Delay(5 * 1000);
                Environment.Exit(-1);
            });

            var t2 =
                System.Threading.Tasks.Task.Run(() => { si.info.vcgen.prover.Close(); });

            System.Threading.Tasks.Task.WaitAll(t1, t2);
        }

        // returns a list of blocks followed by a fake assert
        private List<Absy> GetAbsyTrace(StratifiedVC svc, IList<string> labels)
        {
            if (Options.SIBoolControlVC)
                return GetAbsyTraceBoolControlVC(svc);
            else
                return GetAbsyTraceControlFlowVariable(svc, labels);
        }

        private List<Absy> GetAbsyTraceControlFlowVariable(StratifiedVC svc, IList<string> labels)
        {
            if (labels == null)
            {
                labels = si.info.vcgen.prover.CalculatePath(svc.id);
            }
            var ret = new List<Absy>();
            foreach (var label in labels)
            {
                ret.Add(Label2Absy(svc.info.Implementation.Name, label));
            }
            return ret;
        }

        private List<Absy> GetAbsyTraceBoolControlVC(StratifiedVC svc)
        {
            Debug.Assert(Options.UseProverEvaluate, "Must use prover evaluate option with boolControlVC"); 
            
            var ret = new List<Absy>();
            var impl = svc.info.Implementation;
            var block = impl.Blocks[0];

            while (true)
            {
                ret.Add(block);
                var gc = block.TransferCmd as GotoCmd;
                if (gc == null) break;
                Block next = null;
                foreach (var succ in gc.LabelTargets)
                {
                    var succtaken = svc.info.vcgen.prover.Evaluate(svc.blockToControlVar[succ]).Result;
                    if (succtaken)
                    {
                        next = succ;
                        break;
                    }
                }
                Debug.Assert(next != null, "Must find a successor");
                Debug.Assert(!ret.Contains(next), "CFG cannot be cyclic");
                block = next;
            }

            // fake assert
            ret.Add(new AssertCmd(Token.NoToken, Expr.True));

            return ret;
        }

        private Counterexample NewTrace(StratifiedVC svc, List<Absy> absyList, Model model)
        {
            // assume that the assertion is in the last place??
            AssertCmd assertCmd = (AssertCmd)absyList[absyList.Count - 1];
            List<Block> trace = new List<Block>();
            var CalleeCounterexamples = new Dictionary<TraceLocation, CalleeCounterexampleInfo>();
            for (int j = 0; j < absyList.Count - 1; j++)
            {
                Block b = (Block)absyList[j];
                trace.Add(b);
                if (svc.callSites.ContainsKey(b))
                {
                    foreach (StratifiedCallSite scs in svc.callSites[b])
                    {
                        if (!si.attachedVC.ContainsKey(scs))
                        {
                            if (callSitesToExpand == null)
                                callSitesToExpand = new List<StratifiedCallSite>();

                            callSitesToExpand.Add(scs);
                        }
                        else
                        {
                            List<Absy> calleeAbsyList = GetAbsyTrace(si.attachedVC[scs], null);
                            var calleeCounterexample = NewTrace(si.attachedVC[scs], calleeAbsyList, model);
                            CalleeCounterexamples[new TraceLocation(trace.Count - 1, scs.callSite.numInstr)] =
                            new CalleeCounterexampleInfo(calleeCounterexample, new List<object>());
                        }
                    }
                }
                if (svc.recordProcCallSites.ContainsKey(b) && (model != null || Options.UseProverEvaluate))
                {
                    foreach (StratifiedCallSite scs in svc.recordProcCallSites[b])
                    {
                        var args = new List<object>();
                        foreach (VCExpr expr in scs.interfaceExprs)
                        {
                            if (model == null && Options.UseProverEvaluate)
                            {
                                args.Add(svc.info.vcgen.prover.Evaluate(expr));
                            }
                            else
                            {
                                if (expr is VCExprIntLit)
                                {
                                    args.Add(model.MkElement((expr as VCExprIntLit).Val.ToString()));
                                }
                                else if (expr == VCExpressionGenerator.True)
                                {
                                    args.Add(model.MkElement("true"));
                                }
                                else if (expr == VCExpressionGenerator.False)
                                {
                                    args.Add(model.MkElement("false"));
                                }
                                else if (expr is VCExprVar)
                                {
                                    var idExpr = expr as VCExprVar;
                                    var prover = svc.info.vcgen.prover;
                                    string name = prover.Context.Lookup(idExpr);
                                    Model.Func f = model.TryGetFunc(name);
                                    if (f != null)
                                    {
                                        var val = f.GetConstant();
                                        if (val is Model.DatatypeValue)
                                        {
                                            args.Add(GenerateTraceValue(val));
                                        }
                                        else
                                        {
                                            args.Add(val);
                                        }
                                    }
                                }
                                else
                                {
                                    Debug.Assert(false);
                                }
                            }
                        }
                        CalleeCounterexamples[new TraceLocation(trace.Count - 1, scs.callSite.numInstr)] =
                            new CalleeCounterexampleInfo(null, args);
                    }
                }
            }

            Block lastBlock = (Block)absyList[absyList.Count - 2];
            Counterexample newCounterexample = VerificationConditionGenerator.AssertCmdToCounterexample(assertCmd, lastBlock.TransferCmd, trace, null, model, svc.info.mvInfo, si.info.vcgen.prover.Context);
            newCounterexample.AddCalleeCounterexample(CalleeCounterexamples);
            return newCounterexample;
        }

        private String GenerateTraceValue(Model.Element element)
        {
            var str = new System.IO.StringWriter();
            if (element is Model.DatatypeValue)
            {
                var val = (Model.DatatypeValue)element;
                if (val.ConstructorName == "_" && val.Arguments[0].ToString() == "(as-array)")
                {
                    var parens = val.Arguments[1].ToString();
                    var func = element.Model.TryGetFunc(parens.Substring(1, parens.Length - 2));
                    if (func != null)
                    {
                        str.Write("{");
                        var appCount = 0;
                        foreach (var app in func.Apps)
                        {
                            if (appCount++ > 0)
                                str.Write(",");
                            str.Write("\"");
                            var argCount = 0;
                            foreach (var arg in app.Args)
                            {
                                if (argCount++ > 0)
                                    str.Write(",");
                                str.Write(GenerateTraceValue(arg));
                            }
                            str.Write("\":{0}", GenerateTraceValue(app.Result));
                        }
                        if (func.Else != null)
                        {
                            if (func.AppCount > 0)
                                str.Write(",");
                            str.Write("\"*\":{0}", GenerateTraceValue(func.Else));
                        }
                        str.Write("}");
                    }
                }
            }
            if (str.ToString() == "")
                str.Write(element.ToString().Replace(" ", "").Replace("(", "").Replace(")", ""));
            return str.ToString();
        }
    }

}
