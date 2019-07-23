package info.nightscout.androidaps.database.daos

import androidx.room.Dao
import androidx.room.Query
import info.nightscout.androidaps.database.TABLE_CARBS
import info.nightscout.androidaps.database.entities.Carbs

@Suppress("FunctionName")
@Dao
abstract class CarbsDao : BaseDao<Carbs>() {

    @Query("SELECT * FROM $TABLE_CARBS WHERE id = :id")
    abstract override fun findById(id: Long): Carbs?

    @Query("DELETE FROM $TABLE_CARBS")
    abstract override fun deleteAllEntries()
}