using System.Collections.Generic;

namespace FolThresholdParser.FolThresholdEntities
{
    public interface IExpression
    {
        IEnumerable<string> Variables { get; }
    }
}