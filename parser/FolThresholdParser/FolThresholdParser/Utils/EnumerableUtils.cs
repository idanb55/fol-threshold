using System.Collections.Generic;
using System.Linq;

namespace FolThresholdParser.Utils
{
    public static class EnumerableUtils
    {
        public static Dictionary<TKey, TValue> ToDict<TKey, TValue>(this IEnumerable<KeyValuePair<TKey, TValue>> pairs)
        {
            return pairs.ToDictionary(pair => pair.Key, pair => pair.Value);
        }
    }
}
