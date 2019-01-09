using System.Collections.Generic;
using System.Linq;
using FolThresholdParser.BapaFormula;
using FolSyntax;

namespace FolThresholdParser.VennDiagram
{
    public static class VennDiagramIterator
    {
        private static IEnumerable<BapaSetExpression> ReadMask(int mask, IReadOnlyList<BapaSetExpression> variables, bool useComplement)
        {
            for (var j = 0; j < variables.Count; ++j)
            {
                if ((mask & (1 << j)) == 0)
                {
                    yield return variables[j];
                }
                else if(useComplement)
                    yield return new BapaSetComplement(variables[j]);
            }
        }

        public static IEnumerable<BapaSetExpression> GetVennZonesHelper(SetVarExpression[] variables)
        {
            for (var i = 0; i < 1 << variables.Length; ++i)
            {
                yield return new BapaSetOperation(BapaSetOperation.SetRelation.Intersection, ReadMask(i, variables.Select(var => var.ToBapaSetExpression()).ToArray(), true).ToArray());
            }
        }

        public static IEnumerable<BapaSetExpression> GetVennZones(SetVarExpression[] variables)
        {
            var basicZones = GetVennZonesHelper(variables).ToArray();
            for (var i = 0; i < 1 << basicZones.Length; ++i)
            {
                yield return new BapaSetOperation(BapaSetOperation.SetRelation.Union, ReadMask(i, basicZones, false).ToArray());
            }
        }
    }
}
