using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;

namespace ModCollector
{
    public static class Utils {
        public static ModSetCollector msc = new ModSetCollector();
    }
    public class ModSetCollector : ReadOnlyVisitor
    {
        private Procedure enclosingProc;

        private Dictionary<Procedure /*!*/, HashSet<Variable /*!*/> /*!*/> /*!*/
          modSets;

        private HashSet<Procedure> yieldingProcs;

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(cce.NonNullDictionaryAndValues(modSets));
            Contract.Invariant(Contract.ForAll(modSets.Values, v => cce.NonNullElements(v)));
        }

        public ModSetCollector()
        {
            modSets = new Dictionary<Procedure /*!*/, HashSet<Variable /*!*/> /*!*/>();
            yieldingProcs = new HashSet<Procedure>();
        }

        private bool moreProcessingRequired;

        public void DoModSetAnalysis(Program program)
        {
            Contract.Requires(program != null);

            HashSet<Procedure /*!*/> implementedProcs = new HashSet<Procedure /*!*/>();
            foreach (var impl in program.Implementations)
            {
                if (impl.Proc != null)
                {
                    implementedProcs.Add(impl.Proc);
                }
            }

            foreach (var proc in program.Procedures)
            {
                if (!implementedProcs.Contains(proc))
                {
                    enclosingProc = proc;
                    foreach (var expr in proc.Modifies)
                    {
                        Contract.Assert(expr != null);
                        ProcessVariable(expr.Decl);
                    }

                    enclosingProc = null;
                }
                else
                {
                    if (!modSets.ContainsKey(proc))
                    {
                        modSets.Add(proc, new HashSet<Variable>());
                    }
                }
            }

            moreProcessingRequired = true;
            while (moreProcessingRequired)
            {
                moreProcessingRequired = false;
                this.Visit(program);
            }

            foreach (Procedure x in modSets.Keys)
            {
                x.Modifies = new List<IdentifierExpr>();
                foreach (Variable v in modSets[x])
                {
                    x.Modifies.Add(new IdentifierExpr(v.tok, v));
                }
            }

            foreach (Procedure x in yieldingProcs)
            {
                if (!QKeyValueExtensions.FindBoolAttribute(x.Attributes, CivlAttributes.YIELDS))
                {
                    x.AddAttribute(CivlAttributes.YIELDS);
                }
            }

#if DEBUG_PRINT
      Console.WriteLine("Number of procedures with nonempty modsets = {0}", modSets.Keys.Count);
      foreach (Procedure/*!*/ x in modSets.Keys) {
        Contract.Assert(x != null);
        Console.Write("{0} : ", x.Name);
        bool first = true;
        foreach (Variable/*!*/ y in modSets[x]) {
          Contract.Assert(y != null);
          if (first)
            first = false;
          else
            Console.Write(", ");
          Console.Write("{0}", y.Name);
        }
        Console.WriteLine("");
      }
#endif
        }

        private void ProcessVariable(Variable var)
        {
            Procedure /*!*/
              localProc = cce.NonNull(enclosingProc);
            if (var == null)
                return;
            if (!(var is GlobalVariable))
                return;
            if (!modSets.ContainsKey(localProc))
            {
                modSets[localProc] = new HashSet<Variable /*!*/>();
            }

            if (modSets[localProc].Contains(var))
                return;
            moreProcessingRequired = true;
            modSets[localProc].Add(var);
        }
    }

}