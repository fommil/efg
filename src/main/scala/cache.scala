package fommil.cache

// cache of the most recently accessed (evicting the least recently accessed)
final class LRA[K, V](max_size: Int) extends java.util.LinkedHashMap[K, V](max_size, 1.0f, true) {
  override def removeEldestEntry(eldest: java.util.Map.Entry[K, V]): Boolean = size() >= max_size
}

// cache of the most recently updated items (evicting the least recently updated)
final class LRU[K, V](max_size: Int) extends java.util.LinkedHashMap[K, V](max_size, 1.0f, false) {
  override def removeEldestEntry(eldest: java.util.Map.Entry[K, V]): Boolean = size() >= max_size
}
