using System.Collections.Generic;

namespace FolThresholdParser
{
    public interface IExpression
    {
        IEnumerable<string> Variables { get; }
    }
}