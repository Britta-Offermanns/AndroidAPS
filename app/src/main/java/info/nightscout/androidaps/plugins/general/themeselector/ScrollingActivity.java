package info.nightscout.androidaps.plugins.general.themeselector;

import android.os.Bundle;
import android.view.View;
import android.widget.CompoundButton;
import android.widget.LinearLayout;

import androidx.appcompat.app.AppCompatDelegate;
import androidx.appcompat.widget.SwitchCompat;
import androidx.recyclerview.widget.DefaultItemAnimator;
import androidx.recyclerview.widget.GridLayoutManager;
import androidx.recyclerview.widget.RecyclerView;

import com.google.android.material.bottomsheet.BottomSheetBehavior;

import java.util.ArrayList;
import java.util.List;

import info.nightscout.androidaps.MainActivity;
import info.nightscout.androidaps.R;
import info.nightscout.androidaps.plugins.general.themeselector.adapter.RecyclerViewClickListener;
import info.nightscout.androidaps.plugins.general.themeselector.adapter.ThemeAdapter;
import info.nightscout.androidaps.plugins.general.themeselector.model.Theme;
import info.nightscout.androidaps.plugins.general.themeselector.util.ThemeUtil;
import info.nightscout.androidaps.plugins.general.themeselector.view.ThemeView;
import info.nightscout.androidaps.utils.SP;

public class ScrollingActivity extends MainActivity implements View.OnClickListener{
    public static List<Theme> mThemeList = new ArrayList<>();
    public static int selectedTheme = 0;
    private RecyclerView mRecyclerView;
    private ThemeAdapter mAdapter;
    private BottomSheetBehavior mBottomSheetBehavior;

    @Override
    public void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);

        setContentView(R.layout.themeselector_scrolling_fragment);

        initBottomSheet();

        prepareThemeData();

        ThemeView themeView = findViewById(R.id.theme_selected);
        themeView.setTheme(mThemeList.get(MainActivity.mTheme));
    }

    private void initBottomSheet(){
        // get the bottom sheet view
        LinearLayout llBottomSheet = (LinearLayout) findViewById(R.id.bottom_sheet);

        // init the bottom sheet behavior
        mBottomSheetBehavior = BottomSheetBehavior.from(llBottomSheet);

        SwitchCompat switchCompat = findViewById(R.id.switch_dark_mode);
        switchCompat.setChecked(mIsNightMode);
        switchCompat.setOnCheckedChangeListener(new CompoundButton.OnCheckedChangeListener() {
            @Override
            public void onCheckedChanged(CompoundButton compoundButton, boolean b) {
                mIsNightMode = b;
                SP.putBoolean("daynight", mIsNightMode);
                int delayTime = 200;
                if(mBottomSheetBehavior.getState() == BottomSheetBehavior.STATE_EXPANDED){
                    delayTime = 400;
                    mBottomSheetBehavior.setState(BottomSheetBehavior.STATE_COLLAPSED);
                }
                compoundButton.postDelayed(new Runnable() {
                    @Override
                    public void run() {
                        if(mIsNightMode){
                            getDelegate().setLocalNightMode(AppCompatDelegate.MODE_NIGHT_YES);
                        }else{
                            getDelegate().setLocalNightMode(AppCompatDelegate.MODE_NIGHT_NO);
                        }
                        changeTheme(selectedTheme);
                    }
                },delayTime);

            }
        });

        mRecyclerView = findViewById(R.id.recyclerView);

        mAdapter = new ThemeAdapter(mThemeList, new RecyclerViewClickListener() {
            @Override
            public void onClick(View view, int position) {
                mBottomSheetBehavior.setState(BottomSheetBehavior.STATE_COLLAPSED);
                view.postDelayed(new Runnable() {
                    @Override
                    public void run() {
                       ScrollingActivity.this.recreate();
                       changeTheme(selectedTheme);
                    }
                },500);
            }
        });

        RecyclerView.LayoutManager mLayoutManager = new GridLayoutManager(getApplicationContext(),4);
        mRecyclerView.setLayoutManager(mLayoutManager);
        mRecyclerView.setItemAnimator(new DefaultItemAnimator());
        mRecyclerView.setAdapter(mAdapter);
    }

    private void prepareThemeData() {
        mThemeList.clear();
        mThemeList.addAll(ThemeUtil.getThemeList());
        mAdapter.notifyDataSetChanged();
    }


    @Override
    public void onClick(View view) {
        switch (view.getId()){
            case R.id.theme_selected :
            case R.id.fab:
                // change the state of the bottom sheet
                switch (mBottomSheetBehavior.getState()){
                    case BottomSheetBehavior.STATE_HIDDEN :
                        mBottomSheetBehavior.setState(BottomSheetBehavior.STATE_COLLAPSED);
                        break;

                    case BottomSheetBehavior.STATE_COLLAPSED :
                        mBottomSheetBehavior.setState(BottomSheetBehavior.STATE_EXPANDED);
                        break;

                    case BottomSheetBehavior.STATE_EXPANDED :
                        mBottomSheetBehavior.setState(BottomSheetBehavior.STATE_COLLAPSED);
                        break;
                }
                break;
        }
    }


}
