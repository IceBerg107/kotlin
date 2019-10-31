@Throws(<!UNRESOLVED_REFERENCE, UNRESOLVED_REFERENCE!>IOException<!>::class, <!UNRESOLVED_REFERENCE, UNRESOLVED_REFERENCE!>ResponseParseException<!>::class)
fun fetchPluginReleaseDate(pluginId: PluginId, version: String, channel: String?): LocalDate? {
    val url = "https://plugins.jetbrains.com/api/plugins/${pluginId.<!UNRESOLVED_REFERENCE, UNRESOLVED_REFERENCE!>idString<!>}/updates?version=$version"

    val pluginDTOs: Array<PluginDTO> = try {
        <!UNRESOLVED_REFERENCE, UNRESOLVED_REFERENCE!>HttpRequests<!>.<!UNRESOLVED_REFERENCE!><!UNRESOLVED_REFERENCE!>request<!>(url)<!>.<!UNRESOLVED_REFERENCE, UNRESOLVED_REFERENCE!><!UNRESOLVED_REFERENCE!>connect<!> {
            GsonBuilder().create().fromJson(it.inputStream.reader(), Array<PluginDTO>::class.java)
        }<!>
    } catch (ioException: JsonIOException) {
        throw <!UNRESOLVED_REFERENCE!><!UNRESOLVED_REFERENCE!>IOException<!>(ioException)<!>
    } catch (syntaxException: JsonSyntaxException) {
        throw <!UNRESOLVED_REFERENCE!><!UNRESOLVED_REFERENCE!>ResponseParseException<!>("Can't parse json response", syntaxException)<!>
    }
}

interface AutoCloseable {
    fun close()
}

internal fun AutoCloseable?.closeFinally(cause: Throwable?) = when {
    this == null -> {}
    cause == null -> close()
    else ->
        try {
            close()
        } catch (closeException: Throwable) {
            cause.addSuppressed(closeException)
        }
}

inline fun <reified T : Any> Sequence<*>.firstIsInstanceOrNull(): T? {
    for (element in this) if (element is T) return element
    return null
}